"""Count the exceptional distinct odd piles, without traversing game positions (Python 3.9+)."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb, factorial, gcd, prod
import sys

EDGES = tuple(combinations(range(4), 2))
PRIMES = (3, 5, 7, 11, 13, 17)


def edge_labelings(primes):
    """One of the 6!/4! labelings per orbit under relabeling the four piles."""
    orbit_maps = [
        tuple(EDGES.index(tuple(sorted((order[i], order[j])))) for i,j in EDGES)
        for order in permutations(range(4))
    ]
    for labels in permutations(primes):
        if labels == min(tuple(labels[i] for i in indices) for indices in orbit_maps):
            yield labels


def allowed_sizes(vertex, labels, n):
    outside = prod(p for (i, j), p in zip(EDGES, labels) if vertex not in (i, j))
    inside = prod(labels) // outside
    return [x for x in range(outside, n, 2*outside) if gcd(x, inside) == 1]


def count_by_pair_sums(primes, n):
    """Count positive sizes summing to n for each intrinsic prime-edge labeling."""
    count = 0
    for labels in edge_labelings(primes):
        sizes = [allowed_sizes(i, labels, n) for i in range(4)]
        left = Counter(a+b for a in sizes[0] for b in sizes[1] if a+b < n)
        count += sum(left.get(n-c-d, 0) for c in sizes[2] for d in sizes[3] if c+d < n)
    return count


def residue_histogram(primes):
    """Independent count by the Chinese remainder theorem, one residue variable per edge."""
    radical = prod(primes)
    modulus = 2 * radical
    histogram = Counter()
    for labels in edge_labelings(primes):
        weights = [(modulus//p) * pow(modulus//p, -1, p) for p in labels]
        # A residue starts at radical to set the parity bit. Every edge
        # contributes opposite residues at its two endpoints.
        contributions = [tuple((z*w) % modulus for z in range(1,p))
                         for p,w in zip(labels, weights)]
        for u,v,w,x,y,z in product(*contributions):
            residues = ((radical+u+v+w) % modulus, (radical-u+x+y) % modulus,
                        (radical-v-x+z) % modulus, (radical-w-y-z) % modulus)
            total = sum(residues)
            assert total % modulus == 0
            histogram[total//modulus] += 1
    return histogram


def residue_weight(r, primes):
    edges = comb(r, 2)
    return sum((-1)**j * comb(edges, j) * prod(p**(r-1) - 1 - j*(p-1) for p in primes)
               for j in range(edges + 1))


def ordered_histogram(r, primes):
    """CRT over all eligible local supports, pruning impossible edge covers."""
    edges = tuple(combinations(range(r), 2))
    edge_bits = {edge: 1 << i for i, edge in enumerate(edges)}
    radical = prod(primes)
    modulus = 2 * radical
    target = (1 << len(edges)) - 1
    local = []
    for p in primes:
        weight = (modulus // p) * pow(modulus // p, -1, p)
        options = []
        for head in product(range(p), repeat=r-1):
            v = head + ((-sum(head)) % p,)
            support = tuple(i for i, x in enumerate(v) if x)
            if support:
                options.append((edge_bits.get(support, 0), tuple(weight*x for x in v)))
        local.append(options)
    histogram = Counter()
    def visit(index, covered, residues):
        missing = bin(target ^ covered).count("1")
        remaining = len(primes) - index
        if missing > remaining:
            return
        if remaining == 0:
            total = sum(x % modulus for x in residues)
            offset = radical if r % 2 else 0
            assert (total - offset) % modulus == 0
            histogram[(total - offset) // modulus] += 1
            return
        for bit, increment in local[index]:
            if missing == remaining and (bit == 0 or covered & bit):
                continue
            visit(index + 1, covered | bit, tuple(a+b for a,b in zip(residues, increment)))
    visit(0, 0, (radical,) * r)
    return histogram


def odd_prime_divisors(n):
    while n % 2 == 0:
        n //= 2
    primes = []
    p = 3
    while p*p <= n:
        if n % p == 0:
            primes.append(p)
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        primes.append(n)
    return tuple(primes)


def partition_tables(limit):
    """Euler's pentagonal identity for P(x) and Q(x) = P(x) / P(x^2)."""
    pentagonal = []
    k = 1
    while k*(3*k-1)//2 <= limit:
        sign = 1 if k % 2 else -1
        pentagonal.extend((offset, sign) for offset in (k*(3*k-1)//2, k*(3*k+1)//2)
                          if offset <= limit)
        k += 1
    ordinary = [1]
    distinct = [1]
    for n in range(1, limit+1):
        value = 0
        for offset, sign in pentagonal:
            if offset > n:
                break
            value += sign * ordinary[n-offset]
        ordinary.append(value)
        distinct_value = value
        for offset, sign in pentagonal:
            if 2*offset > n:
                break
            distinct_value -= sign * ordinary[n-2*offset]
        distinct.append(distinct_value)
    return ordinary, distinct


def missing_counts(n):
    """Return (all unreachable positions, unreachable terminal positions)."""
    if n < 1:
        raise ValueError("The number of stones must be positive")
    primes = odd_prime_divisors(n)
    if not primes:
        return 0, 0
    radical = prod(primes)
    ordinary, distinct = partition_tables(n // min(primes))
    all_missing = terminal_missing = 0
    for size in range(1, len(primes)+1):
        sign = 1 if size % 2 else -1
        for subset in combinations(primes, size):
            quotient = n // prod(subset)
            all_missing += sign * ordinary[quotient]
            terminal_missing += sign * distinct[quotient]
    if n % 2 == 0:
        phi = n // (2*radical) * prod(p-1 for p in primes)
        all_missing += phi // 2
        terminal_missing += phi // 2
    r = 3 if n % 2 else 4
    h = n // (2*radical)
    while comb(r, 2) <= len(primes):
        if r == 4 and len(primes) == 6:
            bins = residue_histogram(primes)  # Already unordered.
            divisor = 1
        else:
            bins = ordered_histogram(r, primes)
            divisor = factorial(r)
        weighted = sum(count * comb(h-t+r-1, r-1) for t,count in bins.items() if t <= h)
        extra, remainder = divmod(weighted, divisor)
        assert remainder == 0
        all_missing += extra
        terminal_missing += extra
        r += 2
    return all_missing, terminal_missing


def exceptional_triples(n):
    """Direct arithmetic test on increasing triples of positive odd piles."""
    assert n % 2 == 1
    count = 0
    for a in range(1, n//3 + 1, 2):
        ga = gcd(a,n)
        if ga == 1:
            continue
        for b in range(a+2, (n-a+1)//2, 2):
            c = n-a-b
            if gcd(b,n)>1 and gcd(c,n)>1 and gcd(ga,b)==1:
                count += 1
    return count


if __name__ == "__main__":
    if len(sys.argv) == 2:
        n = int(sys.argv[1])
        all_missing, terminal_missing = missing_counts(n)
        print(f"{n} stones: {all_missing} unreachable; {terminal_missing} unreachable terminal.")
        sys.exit(0)
    if len(sys.argv) > 1:
        raise SystemExit("Usage: python3 count.py [total]")
    assert missing_counts(1) == (0, 0) and missing_counts(10) == (4, 3)
    assert missing_counts(105) == (15833, 685)
    for primes in ((3,5,7), (3,5,11), (3,7,11), (3,5,7,11)):
        radical = prod(primes)
        first = exceptional_triples(radical)
        coefficient = residue_weight(3, primes) // factorial(3)
        for multiplier in (1,3,5) if 5 in primes else (1,3,7):
            k = (multiplier-1)//2
            assert exceptional_triples(radical*multiplier) == first + coefficient*comb(k+1,2)
        print(f"Odd radical {radical}: base {first}, binomial coefficient {coefficient}")
    n = 2*prod(PRIMES)
    cert = residue_histogram(PRIMES)
    by_sums = count_by_pair_sums(PRIMES, n)
    assert cert == {1: 461560, 2: 1841680, 3: 461560}
    assert cert[1] == by_sums
    assert sum(cert.values()) * factorial(4) == residue_weight(4, PRIMES)
    print("Four-pile histogram modulo", n, sorted(cert.items()))
    print("Pair-sum enumeration at", n, by_sums)
    second = count_by_pair_sums(PRIMES, 2*n)
    assert second == 4*cert[1] + cert[2] == 460800*2**3 + 760*2
    print("Pair-sum enumeration at", 2*n, second)
