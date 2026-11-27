#include <algorithm>
#include <iostream>
#include <numeric>
#include <vector>

// Exact, segmented factorization of every integer through B.
// Each output row has n, phi(n), pi(n) for phi(n) <= 3*pi(n), in that order.
int main() {
    constexpr int bound = 5 * (1 << 26);
    constexpr int block = 1 << 17;
    std::vector<int> primes;
    for (int x = 2; x <= bound / x; ++x) {
        bool prime = true;
        for (int p : primes) {
            if (p > x / p) break;
            if (x % p == 0) { prime = false; break; }
        }
        if (prime) primes.push_back(x);
    }
    std::ios::sync_with_stdio(false);
    int pi = 0;
    for (int lo = 1; lo <= bound; lo += block) {
        const int hi = std::min(lo + block - 1, bound);
        std::vector<int> rest(hi - lo + 1);
        std::iota(rest.begin(), rest.end(), lo);
        std::vector<int> phi = rest;
        for (int p : primes) {
            if (p > hi / p) break;
            for (int n = (lo + p - 1) / p * p; n <= hi; n += p) {
                const int i = n - lo;
                phi[i] -= phi[i] / p;
                do { rest[i] /= p; } while (rest[i] % p == 0);
            }
        }
        for (int n = lo; n <= hi; ++n) {
            const int i = n - lo;
            if (rest[i] > 1) phi[i] -= phi[i] / rest[i];
            if (n >= 2 && phi[i] == n - 1) ++pi;
            if (n >= 2 && phi[i] <= 3 * pi)
                std::cout << n << ' ' << phi[i] << ' ' << pi << '\n';
        }
    }
    std::cerr << "pi(" << bound << ") = " << pi << '\n';
}
