// Exact solver for the OEIS-linked Chomp three-opening challenge.
//
// Build:
//   g++ -O3 -march=native -DNDEBUG chomp_three_openings.cpp -o chomp
// Run:
//   ./chomp 10 42
//
// A position is a nonincreasing vector x[0] >= ... >= x[K-1] >= 0.
// The poisoned square is not a legal target, so x[0] is enumerated from 1.
// The program performs exact retrograde analysis, not heuristic search.

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <vector>

using std::cerr;
using std::cout;
using std::max_element;
using std::min;
using std::vector;

struct Bits {
    vector<uint64_t> words;
    Bits() = default;
    explicit Bits(uint64_t nbits) : words((nbits + 63) / 64 + 1) {}

    bool get(uint64_t i) const {
        return (words[i >> 6] >> (i & 63)) & 1ULL;
    }
    uint64_t get64(uint64_t i) const {
        const uint64_t q = i >> 6;
        const int s = static_cast<int>(i & 63);
        return s ? (words[q] >> s) | (words[q + 1] << (64 - s)) : words[q];
    }
    void set(uint64_t i) {
        words[i >> 6] |= 1ULL << (i & 63);
    }
    void clear() {
        std::memset(words.data(), 0, words.size() * sizeof(uint64_t));
    }
};

class Solver {
public:
    Solver(int rows, int max_width)
        : K(rows), N(max_width),
          C(max_width + rows + 3, vector<uint64_t>(rows + 3)),
          shadow_sets(rows - 1), x(rows), opening_count(max_width + 1),
          opening_positions(max_width + 1) {
        for (int a = 0; a < static_cast<int>(C.size()); ++a) {
            C[a][0] = 1;
            for (int b = 1; b <= min(a, rows + 1); ++b) {
                __uint128_t z = static_cast<__uint128_t>(C[a - 1][b - 1]) + C[a - 1][b];
                C[a][b] = static_cast<uint64_t>(z);
            }
        }
        for (int i = 0; i < K - 1; ++i) {
            const int suffix_len = K - i - 1;
            shadow_sets[i] = Bits(C[N + suffix_len][suffix_len]);
        }
    }

    void run() {
        for (int top = 1; top <= N; ++top) {
            x[0] = top;
            if (K > 2) shadow_sets[1].clear();
            if (dfs(1, top)) {
                cerr << "FOUND at width " << top << "\n";
                break;
            }
        }

        int maximum = 0;
        for (int w = 1; w <= N; ++w) {
            maximum = std::max(maximum, opening_count[w]);
            if (opening_count[w] >= 2) {
                cout << K << "x" << w << " openings=" << opening_count[w] << "\n";
                for (const auto &p : opening_positions[w]) {
                    cout << "  (";
                    for (int i = 0; i < K; ++i) {
                        if (i) cout << ',';
                        cout << p[i];
                    }
                    cout << ")\n";
                }
            }
        }
        cout << "max=" << maximum << " P=" << p_count
             << " prefixes=" << prefix_count << "\n";
    }

private:
    int K, N;
    vector<vector<uint64_t>> C;
    vector<Bits> shadow_sets;
    vector<int> x;
    vector<int> opening_count;
    vector<vector<vector<int>>> opening_positions;
    uint64_t p_count = 0;
    uint64_t prefix_count = 0;

    uint64_t rank_suffix(int start) const {
        uint64_t rank = 0;
        for (int pos = start; pos < K; ++pos) {
            const int j = K - pos;
            rank += C[x[pos] + j - 1][j];
        }
        return rank;
    }

    void enumerate_shadow(int move_row, int pos, int equal_block_end,
                          int upper, int lower) {
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

    // Mark every later position that can move directly to the current P-position.
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

    void record_if_rectangle_child() {
        const int width = x[0];
        for (int r = 1; r < K; ++r) {
            bool two_level = x[r] < width;
            for (int i = 0; i < r && two_level; ++i) two_level = (x[i] == width);
            for (int i = r; i < K && two_level; ++i) two_level = (x[i] == x[r]);
            if (two_level) {
                ++opening_count[width];
                opening_positions[width].push_back(x);
            }
        }
    }

    // For a fixed first K-1 rows, at most one final row can complete a P-position:
    // two such positions would be joined by a legal move in the last row.
    bool process_prefix() {
        ++prefix_count;
        const int bottom_bound = x[K - 2];
        uint64_t base[64];
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
                for (int i = 0; i < K - 1; ++i) {
                    hit |= shadow_sets[i].get64(base[i] + static_cast<uint64_t>(v0));
                }
                const int len = min(64, bottom_bound - v0 + 1);
                const uint64_t valid = (len == 64) ? ~0ULL : ((1ULL << len) - 1);
                const uint64_t available = (~hit) & valid;
                if (available) {
                    chosen = v0 + __builtin_ctzll(available);
                    break;
                }
            }
        }

        if (chosen < 0) return false;
        x[K - 1] = chosen;
        ++p_count;
        record_if_rectangle_child();
        add_shadow_of_current_p();
        return opening_count[x[0]] >= 3;
    }

    bool dfs(int pos, int bound) {
        if (pos == K - 1) return process_prefix();
        for (int v = 0; v <= bound; ++v) {
            x[pos] = v;
            if (pos + 1 < K - 1) shadow_sets[pos + 1].clear();
            if (dfs(pos + 1, v)) return true;
        }
        return false;
    }
};

int main(int argc, char **argv) {
    if (argc != 3) {
        std::cerr << "usage: " << argv[0] << " ROWS MAX_WIDTH\n";
        return 2;
    }
    Solver solver(std::stoi(argv[1]), std::stoi(argv[2]));
    solver.run();
    return 0;
}
