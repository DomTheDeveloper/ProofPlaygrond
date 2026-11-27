"""Run independent small exhaustive checks and the two larger fixtures."""

from itertools import product
from math import gcd, isqrt
from compress_bits import count_word, decode, query_arguments, separating_window
from local_bits import bit_counts, candidate_bit, floor_sum, midpoint_interval, midpoint_progressions, split_small_list


def prime_small(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def exact_replies(p, q, window):
    n = p*q
    sigma = (p+1)*(q+1)
    replies = []
    for z in query_arguments(n, window):
        power = z//n
        exact_sigma = (2*power-1)*sigma
        replies.append(str(((exact_sigma << (z.bit_length()//2))//z) % 2))
    return "".join(replies)


def test_floors():
    for n, m, a, b in product(range(9), range(1, 14), range(19), range(15)):
        assert floor_sum(n,m,a,b) == sum((a*i+b)//m for i in range(n))


def test_local():
    # Each modulus goes more than two places past the greatest possible valuation.
    moduli = {2: 2**14, 3: 3**9, 5: 5**7}
    squares = {p: {j*j % m for j in range(m)} for p,m in moduli.items()}
    checked = 0
    for n in range(3, 10000, 2):
        if isqrt(n)**2 == n:
            continue
        low, high = midpoint_interval(n)
        for bases in [(2,), (2,3,5)]:
            if any(n % p == 0 for p in bases):
                continue
            rows = midpoint_progressions(n,bases)
            got = sorted(row.first + row.step*i for row in rows for i in range(row.count))
            want = [x for x in range(low,high+1)
                    if all((x*x-n) % moduli[p] in squares[p] for p in bases)]
            assert got == want
            ones = [sum(candidate_bit(n, m, i) for m in want) for i in range(n.bit_length())]
            assert bit_counts(n,rows) == ones
            checked += 1
    return checked


def test_windows():
    primes = [p for p in range(3,501,2) if prime_small(p)]
    cases = 0
    for i,p in enumerate(primes):
        for q in primes[i+1:]:
            if q > 2*p:
                break
            n = p*q
            for budget in (1,5,n.bit_length()**2):
                w = separating_window(n,budget)
                assert w.width <= max(0,(n.bit_length()+1)//2-2)
                assert (w.high-w.low)//(w.span_per_block+1)+1 <= budget
                replies = exact_replies(p,q,w)
                assert decode(n,w,replies) == (p,q)
                histogram = {}
                for m in range(w.low,w.high+1):
                    value = 0
                    for j in range(w.start,w.start+w.width):
                        value = 2*value+candidate_bit(n,m,j)
                    histogram[value] = 1+histogram.get(value,0)
                assert max(histogram.values()) <= budget
                for value in range(1 << w.width):
                    assert count_word(n,w.low,w.high-w.low+1,w,value) == histogram.get(value,0)
            cases += 1
    return cases


def prime_from_order(n, prime_divisors):
    """Lucas criterion, assuming the supplied distinct prime divisors are proven."""
    rem = n-1
    for p in prime_divisors:
        if rem % p:
            return False
        while rem % p == 0:
            rem //= p
    if rem != 1:
        return False
    return any(pow(a,n-1,n)==1 and all(gcd(pow(a,(n-1)//p,n)-1,n)==1 for p in prime_divisors)
               for a in range(2,150))


def test_large():
    p, q = 13326496357100595419, 14978016447079141999
    # Fully factored prime supports of m-1, in increasing m order.
    certificates = {
        2554897: [2,3,17,31,101],
        88272167: [2,1307,33769],
        1340300341: [2,3,5,1709,4357],
        17477889067: [2,3,11,88272167],
        p: [2,29,109,120607,17477889067],
        q: [2,3,2554897,1340300341],
    }
    proven = set()
    for k, primes in certificates.items():
        assert all(d in proven or (d < 10**6 and prime_small(d)) for d in primes)
        assert prime_from_order(k,primes)
        proven.add(k)
    n = p*q
    for budget,width in [(1,62),(128,55),(16384,48)]:
        w = separating_window(n,budget)
        assert w.width == width and decode(n,w,exact_replies(p,q,w)) == (p,q)
    rows = midpoint_progressions(n,(2,3,5))
    size = sum(row.count for row in rows)
    assert size == 8332097118872522
    assert all(0 < ones < size for ones in bit_counts(n,rows))
    p,q = 6473,9463
    assert prime_small(p) and prime_small(q)
    rows = midpoint_progressions(p*q,(2,3,5))
    assert sum(r.count for r in rows) == 9
    assert bit_counts(p*q,rows,[0]) == [1]
    assert candidate_bit(p*q,(p+q)//2,0) == 1
    p,q = 524309,786433
    assert prime_small(p) and prime_small(q)
    rows = midpoint_progressions(p*q,(2,3,5))
    assert sum(r.count for r in rows)==649
    assert split_small_list(p*q,rows,(p*q).bit_length()**2)==(p,q)


if __name__ == "__main__":
    test_floors()
    local_cases = test_local()
    window_cases = test_windows()
    test_large()
    print(f"Passed floor sums, {local_cases} local profiles, {window_cases} balanced prime pairs, and both larger fixtures.")
