// Export the exact Chomp P-positions as sorted combinatorial ranks.
//
// The output is discovery data for the Lean proof-DAG generator.  It is not trusted by Lean.
// The final proof must be checked from generated proof terms.

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using std::min;
using std::vector;

struct Bits {
    vector<uint64_t> words;
    Bits() = default;
    explicit Bits(uint64_t nbits) : words((nbits + 63) / 64 + 1) {}
    bool get(uint64_t i) const { return (words[i >> 6] >> (i & 63)) & 1ULL; }
    uint64_t get64(uint64_t i) const {
        const uint64_t q = i >> 6;
        const int s = static_cast<int>(i & 63);
        return s ? (words[q] >> s) | (words[q + 1] << (64 - s)) : words[q];
    }
    void set(uint64_t i) { words[i >> 6] |= 1ULL << (i & 63); }
    void clear() { std::memset(words.data(), 0, words.size() * sizeof(uint64_t)); }
};

class Solver {
public:
    Solver(int rows, int max_width, const std::string& output)
        : K(rows), N(max_width), C(max_width + rows + 3, vector<uint64_t>(rows + 3)),
          shadow_sets(rows - 1), x(rows), out(output, std::ios::binary) {
        if (K < 2 || K > 63 || N < 1) throw std::runtime_error("unsupported dimensions");
        if (!out) throw std::runtime_error("cannot open output file");
        for (int a = 0; a < static_cast<int>(C.size()); ++a) {
            C[a][0] = 1;
            for (int b = 1; b <= min(a, rows + 1); ++b) {
                __uint128_t z = static_cast<__uint128_t>(C[a - 1][b - 1]) + C[a - 1][b];
                if (z > std::numeric_limits<uint64_t>::max())
                    throw std::runtime_error("rank overflow");
                C[a][b] = static_cast<uint64_t>(z);
            }
        }
        for (int i = 0; i < K - 1; ++i) {
            const int suffix_len = K - i - 1;
            shadow_sets[i] = Bits(C[N + suffix_len][suffix_len]);
        }
    }

    void run() {
        write_header();
        for (int top = 1; top <= N; ++top) {
            x[0] = top;
            if (K > 2) shadow_sets[1].clear();
            dfs(1, top);
        }
        out.flush();
        if (!out) throw std::runtime_error("failed while writing rank database");
        std::cerr << "P=" << p_count << " prefixes=" << prefix_count
                  << " last_rank=" << last_rank << "\n";
    }

private:
    int K, N;
    vector<vector<uint64_t>> C;
    vector<Bits> shadow_sets;
    vector<int> x;
    std::ofstream out;
    uint64_t p_count = 0;
    uint64_t prefix_count = 0;
    uint64_t last_rank = 0;
    bool have_last = false;

    void write_u64(uint64_t v) { out.write(reinterpret_cast<const char*>(&v), sizeof(v)); }
    void write_header() {
        const char magic[8] = {'C', 'H', 'P', 'R', 'A', 'N', 'K', '1'};
        out.write(magic, sizeof(magic));
        write_u64(static_cast<uint64_t>(K));
        write_u64(static_cast<uint64_t>(N));
    }

    uint64_t rank_suffix(int start) const {
        uint64_t rank = 0;
        for (int pos = start; pos < K; ++pos) {
            const int j = K - pos;
            rank += C[x[pos] + j - 1][j];
        }
        return rank;
    }

    void record_p_rank() {
        const uint64_t rank = rank_suffix(0);
        if (have_last && rank <= last_rank) {
            std::cerr << "non-increasing P rank: " << rank << " after " << last_rank << "\n";
            std::abort();
        }
        write_u64(rank);
        last_rank = rank;
        have_last = true;
    }

    void enumerate_shadow(int move_row, int pos, int equal_block_end, int upper, int lower) {
        if (pos > equal_block_end) {
            shadow_sets[move_row].set(rank_suffix(move_row + 1));
            return;
        }
        const int old = x[pos];
        for (int v = lower; v <= upper; ++v) {
            x[pos] = v;
            enumerate_shadow(move_row, pos + 1, equal_block_end, v, lower);
        }
        x[pos] = old;
    }

    void add_shadow_of_current_p() {
        const vector<int> p = x;
        for (int i = 0; i < K - 1; ++i) {
            const int t = x[i];
            int m = i;
            while (m + 1 < K && x[m + 1] == t) ++m;
            const int upper = (i == 0) ? N : x[i - 1];
            if (upper > t) enumerate_shadow(i, i + 1, m, upper, t);
            x = p;
        }
    }

    void process_prefix() {
        ++prefix_count;
        const int bottom_bound = x[K - 2];
        uint64_t base[64];
        base[K - 2] = 0;
        uint64_t acc = 0;
        for (int pos = K - 2; pos >= 1; --pos) {
            const int j = K - pos;
            acc += C[x[pos] + j - 1][j];
            base[pos - 1] = acc;
        }

        int chosen = -1;
        if (bottom_bound < 48) {
            for (int v = 0; v <= bottom_bound; ++v) {
                bool has_p_option = false;
                for (int i = 0; i < K - 1; ++i) {
                    if (shadow_sets[i].get(base[i] + static_cast<uint64_t>(v))) {
                        has_p_option = true;
                        break;
                    }
                }
                if (!has_p_option) {
                    chosen = v;
                    break;
                }
            }
        } else {
            for (int v0 = 0; v0 <= bottom_bound; v0 += 64) {
                uint64_t hit = 0;
                for (int i = 0; i < K - 1; ++i)
                    hit |= shadow_sets[i].get64(base[i] + static_cast<uint64_t>(v0));
                const int len = min(64, bottom_bound - v0 + 1);
                const uint64_t valid = len == 64 ? ~0ULL : ((1ULL << len) - 1);
                const uint64_t available = (~hit) & valid;
                if (available) {
                    chosen = v0 + __builtin_ctzll(available);
                    break;
                }
            }
        }

        if (chosen < 0) return;
        x[K - 1] = chosen;
        ++p_count;
        record_p_rank();
        add_shadow_of_current_p();
    }

    void dfs(int pos, int bound) {
        if (pos == K - 1) {
            process_prefix();
            return;
        }
        for (int v = 0; v <= bound; ++v) {
            x[pos] = v;
            if (pos + 1 < K - 1) shadow_sets[pos + 1].clear();
            dfs(pos + 1, v);
        }
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 4) {
            std::cerr << "usage: " << argv[0] << " ROWS MAX_WIDTH OUTPUT.bin\n";
            return 2;
        }
        Solver(std::stoi(argv[1]), std::stoi(argv[2]), argv[3]).run();
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
}
