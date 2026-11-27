#include <iostream>
#include <vector>

// Independent computation. Eratosthenes provides primality; an Euler linear
// sieve provides cofactor totients. The proven divisibility filters in the
// accompanying note allow the cofactor table to stop at floor(B/30).
int main() {
    constexpr int bound = 5 * (1 << 26);
    const int cap = bound / 30;
    std::vector<int> phi(cap + 1), primes;
    phi[1] = 1;
    for (int k = 2; k <= cap; ++k) {
        if (phi[k] == 0) {
            primes.push_back(k);
            phi[k] = k - 1;
        }
        for (int p : primes) {
            if (p > cap / k) break;
            if (k % p == 0) {
                phi[k * p] = phi[k] * p;
                break;
            }
            phi[k * p] = phi[k] * (p - 1);
        }
    }
    // oddComposite[j] describes 2*j+1, with 1 marked separately.
    std::vector<bool> oddComposite(bound / 2 + 1);
    oddComposite[0] = true;
    for (int p = 3; p <= bound / p; p += 2) {
        if (oddComposite[p / 2]) continue;
        for (int n = p * p; n <= bound; n += 2 * p)
            oddComposite[n / 2] = true;
    }
    std::ios::sync_with_stdio(false);
    int pi = 0;
    for (int n = 2; n <= bound; ++n) {
        if (n == 2 || ((n & 1) && !oddComposite[n / 2])) ++pi;
        const int d = n < (1 << 20) ? 1 : n < (1 << 24) ? 6 : 30;
        if (n % d != 0) continue;
        const int k = n / d;
        int value = phi[k];
        for (int p : {2, 3, 5}) {
            if (d % p == 0) value *= (k % p == 0) ? p : p - 1;
        }
        if (value <= 3 * pi)
            std::cout << n << ' ' << value << ' ' << pi << '\n';
    }
    std::cerr << "pi(" << bound << ") = " << pi << '\n';
}
