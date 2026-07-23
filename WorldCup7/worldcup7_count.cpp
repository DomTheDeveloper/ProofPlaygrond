// Exact counter for n x n nonnegative integer matrices with zero diagonal
// and every row/column sum equal to r.
//
// The recurrence memoizes only two sorted multisets of residual column sums:
// P = columns whose paired forbidden row has already been processed;
// U = columns still paired with an unprocessed row.
//
// Compile: g++ -O3 -std=c++17 worldcup7_count.cpp -o worldcup7_count
// Run:     ./worldcup7_count 7 12

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <unordered_map>
#include <utility>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>

using boost::multiprecision::cpp_int;
using std::pair;
using std::vector;

struct AllocationOption {
    int amount_used;
    vector<unsigned char> residuals;
    unsigned long long multiplicity;
};

class Counter {
public:
    Counter(int n, int r) : n_(n), r_(r), memo_(n + 1) {
        factorial_[0] = 1;
        for (int i = 1; i < 16; ++i) factorial_[i] = factorial_[i - 1] * i;
        if (n_ < 1 || n_ > 10 || r_ < 0 || r_ > 30) {
            throw std::invalid_argument("This compact implementation requires 1 <= n <= 10 and 0 <= r <= 30.");
        }
    }

    cpp_int run() {
        vector<unsigned char> processed;
        vector<unsigned char> unprocessed(n_, static_cast<unsigned char>(r_));
        return count(processed, unprocessed);
    }

private:
    int n_, r_;
    unsigned long long factorial_[16]{};
    vector<std::unordered_map<unsigned long long, cpp_int>> memo_;
    std::map<pair<int, int>, vector<AllocationOption>> option_cache_;

    static unsigned long long encode(const vector<unsigned char>& p,
                                     const vector<unsigned char>& u) {
        // Five bits per residual; one separator value 31.
        unsigned long long key = static_cast<unsigned long long>(u.size());
        int shift = 4;
        for (auto x : p) { key |= static_cast<unsigned long long>(x) << shift; shift += 5; }
        key |= 31ULL << shift; shift += 5;
        for (auto x : u) { key |= static_cast<unsigned long long>(x) << shift; shift += 5; }
        return key;
    }

    const vector<AllocationOption>& options(int capacity, int multiplicity) {
        pair<int, int> cache_key{capacity, multiplicity};
        auto found = option_cache_.find(cache_key);
        if (found != option_cache_.end()) return found->second;

        vector<AllocationOption> out;
        vector<int> frequency(capacity + 1, 0);
        std::function<void(int, int)> generate = [&](int residual, int left) {
            if (residual == capacity) {
                frequency[residual] = left;
                int residual_sum = 0;
                unsigned long long denominator = 1;
                vector<unsigned char> residuals;
                residuals.reserve(multiplicity);
                for (int z = 0; z <= capacity; ++z) {
                    residual_sum += z * frequency[z];
                    denominator *= factorial_[frequency[z]];
                    for (int k = 0; k < frequency[z]; ++k)
                        residuals.push_back(static_cast<unsigned char>(z));
                }
                int used = multiplicity * capacity - residual_sum;
                if (used <= r_) {
                    out.push_back({used, std::move(residuals),
                                   factorial_[multiplicity] / denominator});
                }
                return;
            }
            for (int c = 0; c <= left; ++c) {
                frequency[residual] = c;
                generate(residual + 1, left - c);
            }
        };
        generate(0, multiplicity);
        std::sort(out.begin(), out.end(), [](const auto& a, const auto& b) {
            return a.amount_used < b.amount_used;
        });
        return option_cache_.emplace(cache_key, std::move(out)).first->second;
    }

    cpp_int count(const vector<unsigned char>& p, const vector<unsigned char>& u) {
        const int q = static_cast<int>(u.size());
        if (q == 0) {
            for (auto x : p) if (x != 0) return 0;
            return 1;
        }

        const auto state_key = encode(p, u);
        auto& table = memo_[q];
        auto found = table.find(state_key);
        if (found != table.end()) return found->second;

        cpp_int total = 0;
        for (int first = 0; first < q; ) {
            const int paired_capacity = u[first];
            int after = first + 1;
            while (after < q && u[after] == paired_capacity) ++after;
            const int row_multiplicity = after - first;

            struct Group { int type, capacity, multiplicity; };
            vector<Group> groups;
            for (int i = 0; i < static_cast<int>(p.size()); ) {
                int j = i + 1;
                while (j < static_cast<int>(p.size()) && p[j] == p[i]) ++j;
                groups.push_back({0, p[i], j - i});
                i = j;
            }
            for (int i = 0; i < q; ) {
                int j = i + 1;
                while (j < q && u[j] == u[i]) ++j;
                int m = j - i - (u[i] == paired_capacity ? 1 : 0);
                if (m > 0) groups.push_back({1, u[i], m});
                i = j;
            }

            vector<unsigned char> p_acc, u_acc;
            std::function<void(int, int, unsigned long long)> combine =
                [&](int group_index, int remaining, unsigned long long ways) {
                    if (group_index == static_cast<int>(groups.size())) {
                        if (remaining != 0) return;
                        vector<unsigned char> p2 = p_acc, u2 = u_acc;
                        // The selected row cannot use its paired column, so that
                        // column's residual is unchanged and now becomes processed.
                        p2.push_back(static_cast<unsigned char>(paired_capacity));
                        std::sort(p2.begin(), p2.end());
                        std::sort(u2.begin(), u2.end());
                        total += cpp_int(row_multiplicity) * ways * count(p2, u2);
                        return;
                    }
                    const auto& g = groups[group_index];
                    const auto& opts = options(g.capacity, g.multiplicity);
                    for (const auto& opt : opts) {
                        if (opt.amount_used > remaining) break;
                        auto& destination = (g.type == 0 ? p_acc : u_acc);
                        const auto old_size = destination.size();
                        destination.insert(destination.end(), opt.residuals.begin(), opt.residuals.end());
                        combine(group_index + 1, remaining - opt.amount_used,
                                ways * opt.multiplicity);
                        destination.resize(old_size);
                    }
                };
            combine(0, r_, 1);
            first = after;
        }

        // Summing over the possible first remaining row counts every completion q times.
        cpp_int answer = total / q;
        cpp_int restored = answer;
        restored *= q;
        if (restored != total) throw std::logic_error("non-exact symmetry division");
        table.emplace(state_key, answer);
        return answer;
    }
};

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "usage: " << argv[0] << " n r\n";
        return 2;
    }
    try {
        int n = std::atoi(argv[1]);
        int r = std::atoi(argv[2]);
        Counter counter(n, r);
        auto start = std::chrono::steady_clock::now();
        cpp_int answer = counter.run();
        double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        std::cout << answer << "\n";
        std::cerr << "elapsed_seconds=" << seconds << "\n";
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
}
