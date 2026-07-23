// Build and serialize the exact reduced layered MDD for the Chomp P-position stream.
// Hashes only select candidate buckets; nodes are merged after exact transition comparison.

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
    uint32_t length;
};

struct Layer {
    std::vector<Node> nodes;
    // Packed transition: low six bits symbol, remaining bits child id.
    std::vector<uint32_t> transitions;
    std::vector<uint32_t> table;

    static uint64_t mix(uint64_t x) {
        x ^= x >> 30;
        x *= 0xbf58476d1ce4e5b9ULL;
        x ^= x >> 27;
        x *= 0x94d049bb133111ebULL;
        x ^= x >> 31;
        return x;
    }

    void initialize() { if (table.empty()) table.assign(16, 0); }

    uint64_t signature_hash(const std::vector<std::pair<uint8_t,uint32_t>>& sig) const {
        uint64_t h = 0x9e3779b97f4a7c15ULL ^ sig.size();
        for (const auto [symbol, child] : sig) {
            const uint64_t x = (static_cast<uint64_t>(child) << 6) | symbol;
            h ^= mix(x + 0x517cc1b727220a95ULL + (h << 1));
            h = (h << 23) | (h >> 41);
            h *= 0x94d049bb133111ebULL;
        }
        return mix(h);
    }

    bool equal(const Node& node, const std::vector<std::pair<uint8_t,uint32_t>>& sig) const {
        if (node.length != sig.size()) return false;
        for (size_t i = 0; i < sig.size(); ++i) {
            uint32_t packed = transitions[node.offset + i];
            if ((packed & 63U) != sig[i].first || (packed >> 6) != sig[i].second) return false;
        }
        return true;
    }

    void rehash() {
        std::vector<uint32_t> next(table.size() * 2, 0);
        const size_t mask = next.size() - 1;
        for (uint32_t id = 0; id < nodes.size(); ++id) {
            size_t slot = mix(nodes[id].hash) & mask;
            while (next[slot]) slot = (slot + 1) & mask;
            next[slot] = id + 1;
        }
        table.swap(next);
    }

    uint32_t intern(const std::vector<std::pair<uint8_t,uint32_t>>& sig) {
        initialize();
        if ((nodes.size() + 1) * 10 > table.size() * 7) rehash();
        const uint64_t hash = signature_hash(sig);
        const size_t mask = table.size() - 1;
        size_t slot = mix(hash) & mask;
        while (table[slot]) {
            uint32_t id = table[slot] - 1;
            if (nodes[id].hash == hash && equal(nodes[id], sig)) return id;
            slot = (slot + 1) & mask;
        }
        if (transitions.size() > UINT32_MAX || sig.size() > UINT32_MAX)
            throw std::runtime_error("MDD layer overflow");
        uint32_t id = static_cast<uint32_t>(nodes.size());
        uint32_t offset = static_cast<uint32_t>(transitions.size());
        for (const auto [symbol, child] : sig) {
            if (child >= (1U << 26)) throw std::runtime_error("child id overflow");
            transitions.push_back((child << 6) | symbol);
        }
        nodes.push_back({hash, offset, static_cast<uint32_t>(sig.size())});
        table[slot] = id + 1;
        return id;
    }
};

struct ActiveNode { std::vector<std::pair<uint8_t,uint32_t>> transitions; };

static void write_u32(std::ofstream& out, uint32_t x) {
    out.write(reinterpret_cast<const char*>(&x), sizeof(x));
}
static void write_u64(std::ofstream& out, uint64_t x) {
    out.write(reinterpret_cast<const char*>(&x), sizeof(x));
}

int main(int argc, char** argv) {
    try {
        if (argc != 3) {
            std::cerr << "usage: " << argv[0] << " P_RANKS.bin OUTPUT.mdd\n";
            return 2;
        }
        std::ifstream input(argv[1], std::ios::binary);
        if (!input) throw std::runtime_error("cannot open rank database");
        char magic[8];
        uint64_t rows = 0, width = 0;
        input.read(magic, 8);
        input.read(reinterpret_cast<char*>(&rows), 8);
        input.read(reinterpret_cast<char*>(&width), 8);
        if (!input || std::string(magic, 8) != "CHPRANK1" || rows != 10 || width != 42)
            throw std::runtime_error("invalid rank database");

        std::vector<std::vector<uint64_t>> choose(width + rows + 3,
                                                  std::vector<uint64_t>(rows + 3));
        for (int a = 0; a < static_cast<int>(choose.size()); ++a) {
            choose[a][0] = 1;
            for (int b = 1; b <= std::min<int>(a, rows + 1); ++b)
                choose[a][b] = choose[a - 1][b - 1] + choose[a - 1][b];
        }

        std::array<Layer,10> layers;
        std::array<ActiveNode,10> active;
        std::array<uint8_t,10> edge{}, previous{}, word{};
        bool first = true;
        uint32_t root = 0;

        auto canonicalize = [&](int depth) {
            uint32_t id = layers[depth].intern(active[depth].transitions);
            active[depth].transitions.clear();
            return id;
        };
        auto minimize_to = [&](int common) {
            for (int depth = 9; depth >= common; --depth) {
                uint32_t child = depth == 9 ? 0 : canonicalize(depth + 1);
                active[depth].transitions.push_back({edge[depth], child});
            }
        };

        uint64_t rank = 0, words = 0;
        auto started = std::chrono::steady_clock::now();
        while (input.read(reinterpret_cast<char*>(&rank), 8)) {
            uint64_t remainder = rank;
            int bound = static_cast<int>(width);
            for (int position = 0; position < 10; ++position) {
                int suffix = 10 - position;
                int low = 0, high = bound, value = 0;
                while (low <= high) {
                    int middle = (low + high) / 2;
                    if (choose[middle + suffix - 1][suffix] <= remainder) {
                        value = middle;
                        low = middle + 1;
                    } else high = middle - 1;
                }
                word[position] = static_cast<uint8_t>(value);
                remainder -= choose[value + suffix - 1][suffix];
                bound = value;
            }
            if (remainder) throw std::runtime_error("rank unranking failed");
            int common = 0;
            if (!first) {
                while (common < 10 && previous[common] == word[common]) ++common;
                minimize_to(common);
            }
            for (int depth = common; depth < 10; ++depth) {
                edge[depth] = word[depth];
                if (depth + 1 < 10) active[depth + 1].transitions.clear();
            }
            previous = word;
            first = false;
            ++words;
            if (words % 10000000 == 0) std::cerr << "words=" << words << "\n";
        }
        if (first) throw std::runtime_error("empty rank database");
        minimize_to(0);
        root = canonicalize(0);
        if (layers[0].nodes.size() != 1 || root != 0)
            throw std::runtime_error("unexpected root structure");

        std::ofstream out(argv[2], std::ios::binary);
        if (!out) throw std::runtime_error("cannot open MDD output");
        const char out_magic[8] = {'C','H','M','D','D','0','0','1'};
        out.write(out_magic, 8);
        write_u64(out, words);
        write_u32(out, 10);
        write_u32(out, 42);
        write_u32(out, root);
        write_u32(out, 0);
        for (int d = 0; d < 10; ++d) {
            write_u64(out, layers[d].nodes.size());
            write_u64(out, layers[d].transitions.size());
        }
        for (int d = 0; d < 10; ++d) {
            for (const Node& node : layers[d].nodes) {
                write_u32(out, node.offset);
                write_u32(out, node.length);
            }
            out.write(reinterpret_cast<const char*>(layers[d].transitions.data()),
                      static_cast<std::streamsize>(layers[d].transitions.size() * sizeof(uint32_t)));
        }
        out.flush();
        if (!out) throw std::runtime_error("failed writing MDD");

        uint64_t total_nodes = 1, total_trans = 0;
        for (int d = 0; d < 10; ++d) {
            total_nodes += layers[d].nodes.size();
            total_trans += layers[d].transitions.size();
            std::cout << "depth=" << d << " nodes=" << layers[d].nodes.size()
                      << " transitions=" << layers[d].transitions.size() << "\n";
        }
        double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
        std::cout << "words=" << words << " total_nodes=" << total_nodes
                  << " total_transitions=" << total_trans << " seconds=" << seconds << "\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
}
