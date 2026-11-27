"""Check the totient lower bound directly from the defining divisor sums."""
from array import array
from sys import argv

def verify(limit):
    tau = array("I", [0]) * (limit + 1)
    sigma = array("Q", [0]) * (limit + 1)
    moment = array("Q", [0]) * (limit + 1)
    phi = array("I", range(limit + 1))
    omega = bytearray(limit + 1)
    for d in range(1, limit + 1):
        if d >= 2 and phi[d] == d:
            for n in range(d, limit + 1, d):
                phi[n] -= phi[n] // d
                omega[n] += 1
        for n in range(d, limit + 1, d):
            tau[n] += 1
            sigma[n] += d
        weighted = d * tau[d]
        for n in range(d, limit + 1, d):
            moment[n] += weighted
    tested = odd_branch = 0
    for n in range(2, limit + 1):
        if omega[n] < 2:
            continue
        a = 2 * n * tau[n] - moment[n]
        gap = phi[n] * (a - sigma[n]) - n * (2 * phi[n] - n) * (tau[n] - 1)
        assert gap >= 0, (n, gap)
        if n % 2 and n <= 2 * phi[n]:
            assert a > sigma[n]
            odd_branch += 1
        tested += 1
    print(f"Up to {limit}: {tested} integers with at least two prime divisors; {odd_branch} odd integers in the totient branch.")

if __name__ == "__main__":
    verify(int(argv[1]) if len(argv) > 1 else 200000)
