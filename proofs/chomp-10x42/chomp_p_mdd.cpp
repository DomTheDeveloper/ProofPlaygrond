// Build the exact reduced layered multi-valued decision diagram for the Chomp P-set.
//
// Input is the sorted combinatorial-rank stream produced by chomp_export_p_ranks.cpp.
// Hashes are used only to select candidate buckets: signatures are compared exactly before
// nodes are merged.  This is a certificate-design and measurement tool, not trusted proof code.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

struct Node {
    uint64_t hash;
    uint32_t offset;
    uint8_t length;
    uint8_t padding[3];
};

struct Layer {
    std::vector<Node> nodes;
    // Packed transition: low six bits are the symbol, remaining bits are the child id.
    std::vector<uint32_t> transitions;
    // Open-addressed table containing node id + 1; zero is empty.
    std::vector<uint32_t> table;

    static uint64_t mix(uint64_t x) {
        x ^= x >> 30;
        x *= 0xbf58476d1ce4e5b9ULL;
        x ^= x >> 27;
        x *= 0x94d049bb133111ebULL;
        x ^= x >> 31;
        return x;
    }

    void initialize() {
        if (table.empty()) table.assign(16, 0);
    }

    uint64_t signatureHash(const std::vector<std::pair<uint8_t, uint32_t>>& signature) const {
        uint64_t h = 0x9e3779b97f4a7c15ULL ^ signature.size();
        for (const auto [symbol, child] : signature) {
            const uint64_t x = (static_cast<uint64_t>(child) << 6) | symbol;
            h ^= mix(x + 0x517cc1b727220a95ULL + (h << 1));
            h = (h << 23) | (h >> 41);
            h *= 0x94d049bb133111ebULL;
        }
        return mix(h);
    }

    bool exactlyEqual(const Node& node,
                      const std::vector<std::pair<uint8_t, uint32_t>>& signature) const {
        if (node.length != signature.size()) return false;
        for (size_t i = 0; i < signature.size(); ++i) {
            const uint32_t packed = transitions[node.offset + i];
            if ((packed & 63U) != signature[i].first ||
                (packed >> 6) != signature[i].second) {
                return false;
            }
        }
        return true;
    }

    void rehash() {
        std::vector<uint32_t> next(table.size() * 2, 0);
        const size_t mask = next.size() - 1;
        for (uint32_t id = 0; id < nodes.size(); ++id) {
            size_t slot = mix(nodes[id].hash) & mask;
            while (next[slot] != 0) slot = (slot + 1) & mask;
            next[slot] = id + 1;
        }
        table.swap(next);
    }

    uint32_t intern(const std::vector<std::pair<uint8_t, uint32_t>>& signature) {
        initialize();
        if ((nodes.size() + 1) * 10 > table.size() * 7) rehash();

        const uint64_t hash = signatureHash(signature);
        const size_t mask = table.size() - 1;
        size_t slot = mix(hash) & mask;
        while (table[slot] != 0) {
            const uint32_t id = table[slot] - 1;
            if (nodes[id].hash == hash && exactlyEqual(nodes[id], signature)) return id;
            slot = (slot + 1) & mask;
        }

        if (signature.size() > 255 || transitions.size() > UINT32_MAX)
            throw std::runtime_error("MDD layer overflow");
        const uint32_t id = static_cast<uint32_t>(nodes.size());
        const uint32_t offset = static_cast<uint32_t>(transitions.size());
        for (const auto [symbol, child] : signature) {
            if (child >= (1U << 26)) throw std::runtime_error("MDD child-id overflow");
            transitions.push_back((child << 6) | symbol);
        }
        nodes.push_back({hash, offset, static_cast<uint8_t>(signature.size()), {0, 0, 0}});
        table[slot] = id + 1;
        return id;
    }

    uint64_t allocatedBytes() const {
        return nodes.capacity() * sizeof(Node) + transitions.capacity() * sizeof(uint32_t) +
               table.capacity() * sizeof(uint32_t);
    }
};

struct ActiveNode {
    std::vector<std::pair<uint8_t, uint32_t>> transitions;
};

int main(int argc, char** argv) {
    try {
        if (argc < 2) {
            std::cerr << "usage: " << argv[0] << " P_RANKS.bin [WORD_LIMIT]\n";
            return 2;
        }
        const uint64_t limit = argc > 2 ? std::stoull(argv[2]) : UINT64_MAX;
        std::ifstream input(argv[1], std::ios::binary);
        if (!input) throw std::runtime_error("cannot open rank database");

        char magic[8];
        uint64_t rows = 0;
        uint64_t width = 0;
        input.read(magic, 8);
        input.read(reinterpret_cast<char*>(&rows), 8);
        input.read(reinterpret_cast<char*>(&width), 8);
        if (!input || std::string(magic, 8) != "CHPRANK1" || rows != 10)
            throw std::runtime_error("invalid rank database");

        std::vector<std::vector<uint64_t>> choose(width + rows + 3,
                                                  std::vector<uint64_t>(rows + 3));
        for (int a = 0; a < static_cast<int>(choose.size()); ++a) {
            choose[a][0] = 1;
            for (int b = 1; b <= std::min<int>(a, rows + 1); ++b)
                choose[a][b] = choose[a - 1][b - 1] + choose[a - 1][b];
        }

        std::array<Layer, 10> layers;
        std::array<ActiveNode, 10> active;
        std::array<uint8_t, 10> edge{};
        std::array<uint8_t, 10> previous{};
        std::array<uint8_t, 10> word{};
        bool first = true;

        auto canonicalize = [&](int depth) {
            const uint32_t id = layers[depth].intern(active[depth].transitions);
            active[depth].transitions.clear();
            return id;
        };

        auto minimizeTo = [&](int commonPrefix) {
            for (int depth = 9; depth >= commonPrefix; --depth) {
                const uint32_t child = depth == 9 ? 0 : canonicalize(depth + 1);
                active[depth].transitions.push_back({edge[depth], child});
            }
        };

        uint64_t rank = 0;
        uint64_t words = 0;
        const auto started = std::chrono::steady_clock::now();
        while (words < limit && input.read(reinterpret_cast<char*>(&rank), 8)) {
            uint64_t remainder = rank;
            int bound = static_cast<int>(width);
            for (int position = 0; position < 10; ++position) {
                const int suffixLength = 10 - position;
                int low = 0;
                int high = bound;
                int value = 0;
                while (low <= high) {
                    const int middle = (low + high) / 2;
                    if (choose[middle + suffixLength - 1][suffixLength] <= remainder) {
                        value = middle;
                        low = middle + 1;
                    } else {
                        high = middle - 1;
                    }
                }
                word[position] = static_cast<uint8_t>(value);
                remainder -= choose[value + suffixLength - 1][suffixLength];
                bound = value;
            }
            if (remainder != 0) throw std::runtime_error("rank unranking failed");

            int commonPrefix = 0;
            if (!first) {
                while (commonPrefix < 10 && previous[commonPrefix] == word[commonPrefix])
                    ++commonPrefix;
                minimizeTo(commonPrefix);
            }
            for (int depth = commonPrefix; depth < 10; ++depth) {
                edge[depth] = word[depth];
                if (depth + 1 < 10) active[depth + 1].transitions.clear();
            }
            previous = word;
            first = false;
            ++words;

            if (words % 10000000 == 0) {
                uint64_t nodeCount = 1;
                uint64_t transitionCount = 0;
                uint64_t bytes = 0;
                for (const Layer& layer : layers) {
                    nodeCount += layer.nodes.size();
                    transitionCount += layer.transitions.size();
                    bytes += layer.allocatedBytes();
                }
                const double seconds = std::chrono::duration<double>(
                    std::chrono::steady_clock::now() - started).count();
                std::cerr << "words=" << words << " seconds=" << seconds
                          << " nodes=" << nodeCount << " transitions=" << transitionCount
                          << " allocatedMiB=" << bytes / 1048576 << '\n';
            }
        }

        if (!first) {
            minimizeTo(0);
            canonicalize(0);
        }

        uint64_t nodeCount = 1;  // shared accepting terminal
        uint64_t transitionCount = 0;
        uint64_t bytes = 0;
        std::cout << "words=" << words << '\n';
        for (int depth = 0; depth < 10; ++depth) {
            std::cout << "depth=" << depth << " nodes=" << layers[depth].nodes.size()
                      << " transitions=" << layers[depth].transitions.size() << '\n';
            nodeCount += layers[depth].nodes.size();
            transitionCount += layers[depth].transitions.size();
            bytes += layers[depth].allocatedBytes();
        }
        const double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - started).count();
        std::cout << "total_nodes=" << nodeCount
                  << " total_transitions=" << transitionCount
                  << " allocated_bytes=" << bytes
                  << " seconds=" << seconds << '\n';
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
        return 1;
    }
}
