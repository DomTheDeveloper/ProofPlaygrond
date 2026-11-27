"""Exact-integer seed recurrences, defining binomial sums, and direct framed terms."""
from argparse import ArgumentParser
from fractions import Fraction
from math import comb, isqrt


def seeds(limit):
    a, b = [1, 1], [1, 1]
    for n in range(1, limit):
        left = (n+1)**2 * (5*n*n-4*n+1)
        right = (55*n**4+11*n**3-26*n*n-5*n+5)*a[-1]
        right += (n-1)**2 * (5*n*n+6*n+2)*a[-2]
        term, rem = divmod(right,left)
        assert rem == 0
        a.append(term)
        left = (n+1)**2 * (5*n*n-6*n+2)
        right = (55*n**4-11*n**3-26*n*n+5*n+5)*b[-1]
        right += (n-1)**2 * (5*n*n+4*n+1)*b[-2]
        term, rem = divmod(right,left)
        assert rem == 0
        b.append(term)
    return a, b


def direct_seed(n, offset):
    return sum(comb(n,j)*comb(n-1,j)*comb(n+j-1+offset,j) for j in range(n))


def framed(n, seq):
    terms = [Fraction(1)]
    for j in range(1,n+1):
        terms.append(Fraction(2*n,j)*sum(seq[i]*terms[j-i] for i in range(1,j+1,2)))
    assert terms[-1].denominator == 1
    return terms[-1].numerator


def test(limit):
    arrays = seeds(max(limit,150))
    for i, seq in enumerate(arrays):
        for n in range(1,151):
            assert direct_seed(n,i) == seq[n]
        assert framed(1,seq) == 2 and framed(2,seq) == 8
        assert framed(10,seq) == (3347043208,6038588808)[i]
        assert (framed(10,seq)-framed(2,seq)) % 125 != 0
    valid = 0
    for p in range(7,limit+1,2):
        if any(p%j == 0 for j in range(3,isqrt(p)+1,2)):
            continue
        valid += 1
        for seq in arrays:
            # Symmetric partners s and p-s have the same inverse square.
            half = sum((seq[s] % p) * (seq[p-s] % p) * pow(s,-2,p)
                       for s in range(1,(p+1)//2))
            assert 2*half % p == 0, p
            if p <= 31:
                for m in (1,2,3,4):
                    assert (framed(p*m,seq)-framed(m,seq)) % p**3 == 0
    print("independently verified",valid,"primes through",limit)
    print("checked 300 direct binomial seeds and both counterexamples at the index 10")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("cutoff",type=int)
    limit = parser.parse_args().cutoff
    assert limit >= 7
    test(limit)
