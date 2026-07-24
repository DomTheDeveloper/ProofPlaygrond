// Build the shared normal-play proof DAG reachable from one or more exact P-positions.
//
// The P-rank database and this extractor are untrusted discovery tools.  The resulting DAG must
// be translated to Lean proof terms and checked by the kernel.

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using State = std::array<uint8_t, 63>;

struct Database {
    int K = 0;
    int N = 0;
    std::vector<std::vector<uint64_t>> C;
    std::vector<uint64_t> pRanks;

    explicit Database(const std::string& path) {
        std::ifstream in(path, std::ios::binary);
        if (!in) throw std::runtime_error("cannot open rank database");
        char magic[8];
        in.read(magic, 8);
        if (!in || std::string(magic, 8) != "CHPRANK1")
            throw std::runtime_error("bad rank database magic");
        uint64_t k = 0, n = 0;
        in.read(reinterpret_cast<char*>(&k), 8);
        in.read(reinterpret_cast<char*>(&n), 8);
        if (!in || k < 2 || k > 63 || n > 63) throw std::runtime_error("bad dimensions");
        K = static_cast<int>(k);
        N = static_cast<int>(n);
        in.seekg(0, std::ios::end);
        const uint64_t size = static_cast<uint64_t>(in.tellg());
        if (size < 24 || (size - 24) % 8) throw std::runtime_error("bad database size");
        const uint64_t count = (size - 24) / 8;
        pRanks.resize(count);
        in.seekg(24, std::ios::beg);
        in.read(reinterpret_cast<char*>(pRanks.data()), static_cast<std::streamsize>(count * 8));
        if (!in || !std::is_sorted(pRanks.begin(), pRanks.end()))
            throw std::runtime_error("unsorted rank database");

        C.assign(N + K + 3, std::vector<uint64_t>(K + 3));
        for (int a = 0; a < static_cast<int>(C.size()); ++a) {
            C[a][0] = 1;
            for (int b = 1; b <= std::min(a, K + 1); ++b) {
                __uint128_t z = static_cast<__uint128_t>(C[a - 1][b - 1]) + C[a - 1][b];
                if (z > std::numeric_limits<uint64_t>::max())
                    throw std::runtime_error("rank overflow");
                C[a][b] = static_cast<uint64_t>(z);
            }
        }
    }

    uint64_t rank(const State& s) const {
        uint64_t r = 0;
        for (int pos = 0; pos < K; ++pos) {
            const int j = K - pos;
            r += C[static_cast<int>(s[pos]) + j - 1][j];
        }
        return r;
    }

    bool isP(const State& s) const {
        const uint64_t r = rank(s);
        return std::binary_search(pRanks.begin(), pRanks.end(), r);
    }
};

uint64_t pack(const State& s, int K) {
    uint64_t z = 0;
    for (int i = 0; i < K; ++i) z |= static_cast<uint64_t>(s[i]) << (6 * i);
    return z;
}

State unpack(uint64_t z, int K) {
    State s{};
    for (int i = 0; i < K; ++i) s[i] = static_cast<uint8_t>((z >> (6 * i)) & 63);
    return s;
}

int weight(const State& s, int K) {
    int w = 0;
    for (int i = 0; i < K; ++i) w += s[i];
    return w;
}

std::string show(const State& s, int K) {
    std::ostringstream out;
    out << '(';
    for (int i = 0; i < K; ++i) {
        if (i) out << ',';
        out << static_cast<int>(s[i]);
    }
    out << ')';
    return out.str();
}

std::vector<State> children(const State& p, int K) {
    std::vector<State> out;
    for (int i = 0; i < K; ++i) {
        for (int t = 0; t < p[i]; ++t) {
            if (i == 0 && t == 0) continue;
            State q = p;
            for (int j = i; j < K; ++j) q[j] = std::min<int>(q[j], t);
            out.push_back(q);
        }
    }
    std::sort(out.begin(), out.end(), [K](const State& a, const State& b) {
        return pack(a, K) < pack(b, K);
    });
    out.erase(std::unique(out.begin(), out.end(), [K](const State& a, const State& b) {
        return pack(a, K) == pack(b, K);
    }), out.end());
    return out;
}

State parse(const std::string& text, int K, int N) {
    State s{};
    std::stringstream input(text);
    std::string part;
    int i = 0;
    int previous = N;
    while (std::getline(input, part, ',')) {
        if (i >= K) throw std::runtime_error("root has too many rows");
        const int v = std::stoi(part);
        if (v < 0 || v > N || v > previous) throw std::runtime_error("invalid root");
        s[i++] = static_cast<uint8_t>(v);
        previous = v;
    }
    if (i != K || s[0] == 0) throw std::runtime_error("root has wrong row count or no poison");
    return s;
}

int main(int argc, char** argv) {
    try {
        if (argc < 4) {
            std::cerr << "usage: " << argv[0] << " DB.bin NODE_LIMIT ROOT [ROOT ...]\n";
            return 2;
        }
        Database db(argv[1]);
        const uint64_t limit = std::stoull(argv[2]);
        std::vector<uint64_t> stack;
        std::unordered_set<uint64_t> seen;
        seen.reserve(std::min<uint64_t>(limit * 2, 100000000));

        for (int a = 3; a < argc; ++a) {
            State root = parse(argv[a], db.K, db.N);
            if (!db.isP(root)) throw std::runtime_error("root is not P: " + show(root, db.K));
            const uint64_t key = pack(root, db.K);
            if (seen.insert(key).second) stack.push_back(key);
        }

        uint64_t pNodes = 0;
        uint64_t nNodes = 0;
        uint64_t edges = 0;
        uint64_t maxFan = 0;
        uint64_t reusedReplies = 0;
        uint64_t processed = 0;

        while (!stack.empty()) {
            const uint64_t key = stack.back();
            stack.pop_back();
            const State s = unpack(key, db.K);
            ++processed;
            const auto next = children(s, db.K);

            if (db.isP(s)) {
                ++pNodes;
                edges += next.size();
                maxFan = std::max<uint64_t>(maxFan, next.size());
                for (const State& q : next) {
                    if (db.isP(q))
                        throw std::runtime_error("P node has P child: " + show(s, db.K) +
                                                 " -> " + show(q, db.K));
                    const uint64_t qkey = pack(q, db.K);
                    if (seen.insert(qkey).second) {
                        if (seen.size() > limit) goto limit_hit;
                        stack.push_back(qkey);
                    }
                }
            } else {
                ++nNodes;
                const State* choice = nullptr;
                int bestWeight = std::numeric_limits<int>::max();
                for (const State& q : next) {
                    if (!db.isP(q)) continue;
                    const uint64_t qkey = pack(q, db.K);
                    if (seen.count(qkey)) {
                        choice = &q;
                        ++reusedReplies;
                        break;
                    }
                    const int qWeight = weight(q, db.K);
                    if (qWeight < bestWeight) {
                        bestWeight = qWeight;
                        choice = &q;
                    }
                }
                if (!choice) throw std::runtime_error("N node has no P child: " + show(s, db.K));
                ++edges;
                const uint64_t qkey = pack(*choice, db.K);
                if (seen.insert(qkey).second) {
                    if (seen.size() > limit) goto limit_hit;
                    stack.push_back(qkey);
                }
            }

            if (processed % 1000000 == 0) {
                std::cerr << "processed=" << processed << " seen=" << seen.size()
                          << " P=" << pNodes << " N=" << nNodes
                          << " stack=" << stack.size() << "\n";
            }
        }

        std::cout << "COMPLETE nodes=" << seen.size() << " P=" << pNodes << " N=" << nNodes
                  << " edges=" << edges << " maxFan=" << maxFan
                  << " reused=" << reusedReplies << "\n";
        return 0;

limit_hit:
        std::cout << "LIMIT nodes=" << seen.size() << " processed=" << processed
                  << " P=" << pNodes << " N=" << nNodes << " edges=" << edges
                  << " maxFan=" << maxFan << " reused=" << reusedReplies
                  << " stack=" << stack.size() << "\n";
        return 3;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
}
