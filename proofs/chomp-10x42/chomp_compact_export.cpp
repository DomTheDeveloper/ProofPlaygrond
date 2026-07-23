// Generate a compact explicit closed response carrier for the three 10x42 Chomp roots.
// The P-position MDD is discovery input only. The emitted certificate is replayable without it.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using Position = std::array<uint8_t, 10>;
struct Node { uint32_t offset, length; };
struct Layer { std::vector<Node> nodes; std::vector<uint32_t> transitions; };

struct MDD {
    uint64_t words = 0;
    uint32_t rows = 0, width = 0, root = 0;
    std::array<Layer, 10> layer;
    explicit MDD(const std::string& path) {
        std::ifstream in(path, std::ios::binary);
        if (!in) throw std::runtime_error("cannot open MDD");
        char magic[8]; uint32_t reserved = 0;
        in.read(magic, 8); in.read(reinterpret_cast<char*>(&words), 8);
        in.read(reinterpret_cast<char*>(&rows), 4); in.read(reinterpret_cast<char*>(&width), 4);
        in.read(reinterpret_cast<char*>(&root), 4); in.read(reinterpret_cast<char*>(&reserved), 4);
        if (!in || std::string(magic, 8) != "CHMDD001" || rows != 10 || width != 42)
            throw std::runtime_error("bad MDD header");
        std::array<uint64_t, 10> nodes{}, transitions{};
        for (int d = 0; d < 10; ++d) {
            in.read(reinterpret_cast<char*>(&nodes[d]), 8);
            in.read(reinterpret_cast<char*>(&transitions[d]), 8);
        }
        for (int d = 0; d < 10; ++d) {
            if (nodes[d] > UINT32_MAX || transitions[d] > UINT32_MAX)
                throw std::runtime_error("MDD layer too large");
            layer[d].nodes.resize(nodes[d]); layer[d].transitions.resize(transitions[d]);
            for (Node& n : layer[d].nodes) {
                in.read(reinterpret_cast<char*>(&n.offset), 4);
                in.read(reinterpret_cast<char*>(&n.length), 4);
                if (static_cast<uint64_t>(n.offset) + n.length > transitions[d])
                    throw std::runtime_error("bad node span");
            }
            in.read(reinterpret_cast<char*>(layer[d].transitions.data()),
                    static_cast<std::streamsize>(transitions[d] * 4));
        }
        if (!in || root >= layer[0].nodes.size()) throw std::runtime_error("truncated MDD");
    }
    int32_t step(int depth, uint32_t node, uint8_t symbol) const {
        const Node& n = layer[depth].nodes.at(node);
        uint32_t lo = n.offset, hi = n.offset + n.length;
        while (lo < hi) {
            const uint32_t mid = lo + (hi - lo) / 2;
            const uint32_t packed = layer[depth].transitions[mid];
            const uint8_t s = static_cast<uint8_t>(packed & 63U);
            if (s < symbol) lo = mid + 1; else hi = mid;
        }
        if (lo == n.offset + n.length) return -1;
        const uint32_t packed = layer[depth].transitions[lo];
        return (packed & 63U) == symbol ? static_cast<int32_t>(packed >> 6) : -1;
    }
    bool accepts(const Position& p) const {
        uint32_t node = root;
        for (int d = 0; d < 10; ++d) {
            const int32_t next = step(d, node, p[d]);
            if (next < 0) return false;
            node = static_cast<uint32_t>(next);
        }
        return true;
    }
};

static uint64_t pack(const Position& p) {
    uint64_t z = 0;
    for (int i = 0; i < 10; ++i) z |= static_cast<uint64_t>(p[i]) << (6 * i);
    return z;
}
static Position unpack(uint64_t z) {
    Position p{};
    for (int i = 0; i < 10; ++i) p[i] = static_cast<uint8_t>((z >> (6 * i)) & 63U);
    return p;
}
static int area(const Position& p) {
    int s = 0; for (uint8_t x : p) s += x; return s;
}
static Position bite(const Position& p, int row, int target) {
    Position q = p;
    for (int j = row; j < 10; ++j) q[j] = static_cast<uint8_t>(std::min<int>(q[j], target));
    return q;
}
static std::vector<uint64_t> unique_children(const Position& p) {
    std::vector<uint64_t> out; out.reserve(420);
    for (int row = 0; row < 10; ++row) {
        const int low = row == 0 ? 1 : 0;
        for (int target = low; target < p[row]; ++target) out.push_back(pack(bite(p, row, target)));
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
}
static bool find_move(const Position& from, const Position& to, uint8_t& row_out, uint8_t& target_out) {
    for (int row = 0; row < 10; ++row) {
        const int low = row == 0 ? 1 : 0;
        for (int target = low; target < from[row]; ++target) {
            if (bite(from, row, target) == to) {
                row_out = static_cast<uint8_t>(row);
                target_out = static_cast<uint8_t>(target);
                return true;
            }
        }
    }
    return false;
}

struct Choice { uint64_t key; uint32_t frequency; int area; };
struct Record { uint32_t next; uint8_t row; uint8_t target; uint16_t reserved = 0; };

class Synthesizer {
public:
    Synthesizer(const MDD& mdd, uint64_t limit) : A(mdd), node_limit(limit) {}
    void run(const std::string& output) {
        const std::array<Position, 3> roots = {{
            {{42,42,42,42,35,35,35,35,35,35}},
            {{42,42,42,42,42,42,29,29,29,29}},
            {{42,42,42,42,42,42,42,25,25,25}}
        }};
        for (const Position& root : roots) {
            if (!A.accepts(root)) throw std::runtime_error("root absent from P MDD");
            insert(pack(root));
        }
        while (!stack.empty()) {
            const uint64_t pkey = stack.back(); stack.pop_back();
            process(unpack(pkey)); ++processed;
            if (processed % 10000 == 0)
                std::cerr << "processed=" << processed << " carrier=" << carrier.size()
                          << " responses=" << response.size() << " stack=" << stack.size() << '\n';
        }
        write_certificate(output, roots);
        std::cout << "COMPLETE carrier=" << carrier.size() << " processed=" << processed
                  << " unique_responses=" << response.size() << " opponent_edges=" << opponent_edges
                  << " output=" << output << '\n';
    }
private:
    const MDD& A;
    uint64_t node_limit;
    std::unordered_set<uint64_t> carrier;
    std::unordered_map<uint64_t, uint64_t> response;
    std::vector<uint64_t> stack;
    uint64_t processed = 0, opponent_edges = 0;

    void insert(uint64_t key) {
        if (carrier.insert(key).second) {
            if (carrier.size() > node_limit) throw std::runtime_error("carrier node limit exceeded");
            stack.push_back(key);
        }
    }
    void process(const Position& p) {
        const std::vector<uint64_t> qkeys = unique_children(p);
        opponent_edges += qkeys.size();
        std::vector<std::vector<uint64_t>> options(qkeys.size());
        std::vector<uint8_t> covered(qkeys.size(), 0);
        size_t uncovered = qkeys.size();
        for (size_t qi = 0; qi < qkeys.size(); ++qi) {
            const uint64_t qkey = qkeys[qi];
            auto old = response.find(qkey);
            if (old != response.end()) {
                if (!carrier.count(old->second)) throw std::runtime_error("response leaves carrier");
                covered[qi] = 1; --uncovered; continue;
            }
            const Position q = unpack(qkey);
            if (A.accepts(q)) throw std::runtime_error("carrier P position has P child");
            for (uint64_t rkey : unique_children(q)) if (A.accepts(unpack(rkey))) options[qi].push_back(rkey);
            if (options[qi].empty()) throw std::runtime_error("opponent child has no P reply");
            uint64_t best_existing = 0; int best_area = -1;
            for (uint64_t rkey : options[qi]) if (carrier.count(rkey)) {
                const int a = area(unpack(rkey));
                if (a > best_area || (a == best_area && rkey < best_existing)) {
                    best_existing = rkey; best_area = a;
                }
            }
            if (best_area >= 0) {
                response.emplace(qkey, best_existing);
                covered[qi] = 1; --uncovered;
            }
        }
        if (!uncovered) return;
        std::unordered_map<uint64_t, uint32_t> frequency;
        frequency.reserve(uncovered * 8);
        for (size_t qi = 0; qi < qkeys.size(); ++qi)
            if (!covered[qi]) for (uint64_t rkey : options[qi]) ++frequency[rkey];
        std::vector<Choice> choices; choices.reserve(frequency.size());
        for (const auto& [key, count] : frequency) choices.push_back({key, count, area(unpack(key))});
        std::sort(choices.begin(), choices.end(), [](const Choice& a, const Choice& b) {
            if (a.frequency != b.frequency) return a.frequency > b.frequency;
            if (a.area != b.area) return a.area > b.area;
            return a.key < b.key;
        });
        for (const Choice& choice : choices) {
            if (!uncovered) break;
            bool useful = false;
            for (size_t qi = 0; qi < qkeys.size(); ++qi) {
                if (covered[qi]) continue;
                if (std::binary_search(options[qi].begin(), options[qi].end(), choice.key)) {
                    response.emplace(qkeys[qi], choice.key);
                    covered[qi] = 1; --uncovered; useful = true;
                }
            }
            if (useful) insert(choice.key);
        }
        if (uncovered) throw std::runtime_error("greedy cover failed");
    }
    void write_certificate(const std::string& path, const std::array<Position, 3>& roots) const {
        std::vector<uint64_t> positions(carrier.begin(), carrier.end());
        std::sort(positions.begin(), positions.end());
        std::unordered_map<uint64_t, uint32_t> index;
        index.reserve(positions.size() * 2);
        for (uint32_t i = 0; i < positions.size(); ++i) index.emplace(positions[i], i);
        for (const Position& root : roots) if (!index.count(pack(root))) throw std::runtime_error("root missing");
        uint64_t records = 0;
        for (uint64_t pkey : positions) records += static_cast<uint64_t>(area(unpack(pkey)) - 1);
        std::ofstream out(path, std::ios::binary);
        if (!out) throw std::runtime_error("cannot create certificate");
        out.write("CHCEXP01", 8);
        const uint64_t n = positions.size();
        out.write(reinterpret_cast<const char*>(&n), 8);
        out.write(reinterpret_cast<const char*>(&records), 8);
        out.write(reinterpret_cast<const char*>(positions.data()), static_cast<std::streamsize>(n * 8));
        uint64_t written = 0;
        for (uint64_t pkey : positions) {
            const Position p = unpack(pkey);
            const uint32_t count = static_cast<uint32_t>(area(p) - 1);
            out.write(reinterpret_cast<const char*>(&count), 4);
            for (int first_row = 0; first_row < 10; ++first_row) {
                const int low = first_row == 0 ? 1 : 0;
                for (int first_target = low; first_target < p[first_row]; ++first_target) {
                    const Position q = bite(p, first_row, first_target);
                    const auto it = response.find(pack(q));
                    if (it == response.end()) throw std::runtime_error("missing response");
                    const auto jt = index.find(it->second);
                    if (jt == index.end()) throw std::runtime_error("response not in carrier");
                    const Position r = unpack(it->second);
                    Record rec{}; rec.next = jt->second;
                    if (!find_move(q, r, rec.row, rec.target)) throw std::runtime_error("illegal response");
                    out.write(reinterpret_cast<const char*>(&rec), sizeof(rec));
                    ++written;
                }
            }
        }
        if (!out || written != records) throw std::runtime_error("certificate write failure");
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 4) {
            std::cerr << "usage: " << argv[0] << " P.mdd NODE_LIMIT OUTPUT.bin\n";
            return 2;
        }
        MDD mdd(argv[1]);
        Synthesizer synth(mdd, std::stoull(argv[2]));
        synth.run(argv[3]);
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return std::string(e.what()) == "carrier node limit exceeded" ? 3 : 1;
    }
}
