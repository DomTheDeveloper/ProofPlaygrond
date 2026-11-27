# Recovering balanced factors from a short block of divisor-sum bits

For a product of distinct odd primes `N = p*q` with `p < q <= 2p`, the selector computes, from N alone, a consecutive block of at most half the previous number of binary queries, rounded up. The answers recover both primes. With a larger budget of ordinary arithmetic, fewer answers suffice. The computation of those answers on every input is the unresolved factoring step.

## Results at a glance

Let b be the binary length of N. The bit requested at a positive integer z of binary length L is

```
B(z) = floor(2^floor(L/2) * sigma(z)/z) mod 2.
```

Here sigma sums the positive divisors. All queries are fixed before receiving any answers. The postprocessing also works if an external source supplies just the consecutive word.

| Task | Guarantee |
|---|---|
| Select a block | Deterministic arithmetic polynomial in b. All query inputs have fewer than 9b bits. |
| Factor with one candidate interval | At most ceil(b/2) one-bit answers, plus polynomial bit time. |
| Factor with a budget of T candidate intervals | At most max(0, b/2 − log₂ T + O(1)) one-bit answers and O(T poly(b)) additional bit time. |
| Infer individual replies from local restrictions | Counts both values exactly over the balanced interval after testing square solvability at every power of each selected prime. Polynomial bit time for any fixed number of fixed primes. |
| Always compute all needed replies from N alone | Open. |

The tradeoff applies to unrestricted computations **outside** the oracle as an upper bound. Its matching lower bound later in this note applies only to procedures that must cover every locally possible midpoint with a bounded list.

## Running the implementation

Python 3.10 or later suffices. The scripts use the standard library.

```sh
python check.py
python local_bits.py 412333899797 --primes 2 3 5
python compress_bits.py 1264463 --list-queries
python compress_bits.py 1264463 --replies 10101110
```

The second command uses no oracle. It tests the real size restriction and all powers of 2, 3 and 5, represents 649 surviving midpoints in eight progressions, and recovers 524309 and 786433 by exact square tests. The original real interval has 38,952 integer midpoints.

The last two commands demonstrate selection from N and decoding separately. For this 21-bit input the block starts at zero-based index 15 and has eight replies. Decoding recovers 1039 and 1217. A block may extend past the first b indices of the earlier reduction. The supplied answers in the reproducible tests come from independent evaluation using the known synthetic factors.

## The separating window

Write m=(p+q)/2 and d=(q−p)/2. Then m²−N=d². The assumption on the factor ratio gives the computable interval

```
lo = ceil(sqrt(N)),    hi = floor(sqrt(9N/8)),    W = hi − lo.
```

Indeed, 9pq−2(p+q)²=(2q−p)(2p−q) is nonnegative. Its converse also holds for positive ordered real factors. The width satisfies W < sqrt(N)/16 because 9/8 < (17/16)².

The padded input of index i is zᵢ = 2^(5b+2i) N. The earlier Lean theorem `AbundancePrecision.query_bit` and sigma(N)=N+1+2m give its requested bit as

```
F(j+1) mod 2,    j = 3b+i,    F(k) = floor((2^k(1+2m)−1)/N).
```

Subtracting one accounts for exact division at a binary boundary. Since floor(F(k+1)/2)=F(k), a block of h consecutive answers represents F(j+h) mod P, where P=2^h. Put R=1+((2^j(1+2m)−1) mod N), in [1,N]. The word equals floor((P R−1)/N). Two representatives in the same bin differ by at most H=floor((N−1)/P).

Consider first an interval of width D>0; choose h as the binary length of 3D. Then 3D<P, so 3DH<N. At shift i a collision requires a nonzero signed residue y congruent to Aᵢ x modulo N, with 1≤x≤D and |y|≤H, where Aᵢ=2^(3b+i+1). A zero residue cannot occur since N is odd and D<N.

Suppose consecutive shifts both have such relations (x,y) and (z,v). Then N divides vx−2yz. Its absolute value is at most 3DH<N, so vx=2yz. Thus the signed slope v/z doubles the preceding slope y/x. If every shift from 0 through bit_length(DH) were bad, the absolute slope would start at least 1/D and end greater than H. This contradicts the bound on every slope. A good shift therefore exists within that window. This argument also handles H=0 by immediate separation.

The selector counts d in [1,D] for which Aᵢd mod N falls in [0,H] or [N−H,N). Each count is a difference of Euclidean floor sums. It tries O(b) shifts. At a good shift the selected block separates every interval of width D. To decode, count matches to the observed word on any prefix of such an interval and use binary search. More explicitly, if X=2^(j+h)(1+2m)−1, the indicator for word w is

```
floor((X+(P−w)N)/(PN)) − floor((X+(P−w−1)N)/(PN)).
```

For a budget T≥1 use D=floor(W/T). Consecutive blocks of D+1 midpoints cover the real interval in at most T blocks. Find the at most one match per block and check the resulting integer square. If D=0, direct square tests suffice with zero oracle answers. When D>0 the maximum padded query length is 6b+2(i+h−1)<9b because DH<N/3 and h≤ceil(b/2). All exponents, Euclidean iterations, and binary searches use a polynomial number of bit operations per candidate interval. A polynomial choice of T preserves polynomial work outside the oracle.

## What the congruences can determine

For a candidate midpoint m put G=m²−N. The program handles positive G for odd nonsquare inputs. At 2 it is a square at every precision precisely when G=4^t u with u congruent to 1 modulo 8. For fixed t this is one condition

```
m² ≡ N+4^t   (mod 8*4^t).
```

There are O(b) choices of t and at most four residue classes per choice. For an odd prime ell coprime to N, require even valuation and a nonzero square as the leading unit modulo ell. Distinct valuation classes are disjoint. The program lifts the roots, intersects classes across primes by the Chinese remainder theorem, and clips them to the real interval. Exponents past the binary size of G add no restrictions. The number of classes stays polynomial for a fixed number of fixed primes; the algorithm has no polynomial guarantee when the number of primes grows.

On each resulting arithmetic progression, every numerator of F(k) is affine in the progression index. The identity floor(X/N) mod 2 = floor(X/N)−2 floor(X/(2N)) counts the two replies using Euclidean floor sums. If all surviving midpoints agree, that reply is certified for the promised input. The count describes the information furnished by these tests. Integer square tests may exclude additional candidates.

A majority can give the wrong bit. For N=61,253,999=6473·9463, testing every power of 2, 3 and 5 leaves nine midpoints. Eight give a zero at index zero. The true midpoint 7968 is the only one giving a one.

## A counting limit for this method

For every odd N one entire midpoint class modulo 64 passes **all** dyadic precisions whenever m²≥N. To see this, for N≡3 or 7 modulo 8 choose m so m²−N≡1 modulo 8. For N≡5 modulo 8 choose m²≡N+4 modulo 32. For N≡1 modulo 8 choose m²≡N+16 modulo 128. In the latter two cases the specified right side is an odd square modulo 8 and lifts to every higher power. All squares of integers in the same class modulo 64 agree modulo 128.

Writing t=floor(sqrt(N)), the interval from t+1 through t+64 floor(t/2048) contains at least floor(t/2048) members of any chosen class modulo 64 and lies in the balanced real range. The Lean theorem constructs this many distinct surviving candidates. If an identification procedure must cover every such hidden candidate, and each h-bit transcript can return at most T candidates, then

```
2^h T ≥ floor(floor(sqrt(N))/2048).
```

Within this local-information model the upper and lower bounds differ by a constant number of bits when the right side substantially exceeds T. The inequality does not restrict algorithms that use other properties of the actual integer factorization.

Adding any fixed set of odd primes preserves a positive proportion of candidate midpoints in sufficiently long intervals. For ell≥5 coprime to N, choose a nonzero residue x with x² unequal to N modulo ell. With m=(x+N/x)/2 the difference m²−N is a nonzero square modulo ell, and every midpoint in that class passes at all powers of ell. For ell=3 use m≡0 modulo 3 when N≡2, and a root of m²≡N+9 modulo 27 when N≡1. The Chinese remainder theorem combines the choices. This counting statement concerns simultaneous local solvability.

## Reproduced example

The 128-bit synthetic input was 199604481618592988980642015258549902581. The independent test verifies primality using the Lucas order criterion and complete prime supports of p−1 and q−1. It evaluates the oracle bits directly from the known two primes, 13326496357100595419 and 14978016447079141999.

| Candidate budget T | Start index | Supplied one-bit answers | Decoder outcome |
|---:|---:|---:|---|
| 1 | 6 | 62 | Both factors recovered |
| 128 | 0 | 55 | Both factors recovered |
| 16,384 | 0 | 48 | Both factors recovered |

Testing every power of 2, 3 and 5 leaves exactly 8,332,097,118,872,522 midpoints. Every one of the first 128 bit positions takes both possible values on this set. In particular, the local computation cannot supply the 48-bit word in the last row.

## Verification and prior work

The pinned Lean 4.33.1 project builds with Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. From a fresh project with Lean and Lake installed, run:

```sh
lake update
lake exe cache get
lake build
```

| File | What it checks |
|---|---|
| DoublingWindow.lean | Zero determinants, existence of a separating shift, word packing, and injectivity on intervals |
| LocalBitCertificates.lean | A surviving class at every binary precision, distinct balanced candidates, and the parity-count identity |
| SemiprimeBridge.lean | Connection to the actual divisor-sum bit oracle, the half-length query bound, midpoint uniqueness, recovery of both factors, and list capacity |
| DivisorSumBitReduction.lean | Earlier divisor-sum oracle construction used by the bridge |
| check.py | Exhaustive small reference comparisons, authentic oracle replies generated from the fixture factorizations, and exact arithmetic checks on both larger inputs |

The bit-operation analysis and the general odd-prime extension are written proofs. Python implements the fast counting and decoding procedures. Its equivalence to the formal specifications is tested. The Lean theorems do not use new axioms or proof placeholders.

Shunia's November 25 preprint reduces deterministic general factoring to divisor sums and abundance tests. Its divisor sums at predetermined powers supply the all-input step in the earlier reduction. Its output does not supply the required one-bit answers here. [Deterministic integer factorization from abundance decisions](https://arxiv.org/abs/2611.34242)

The Cogentic November 25 manuscript reports a worst-case deterministic proper-divisor algorithm with time O(exp(3(ln N)^(3/4))). On a b-bit input its stated bound is exp(O(b^(3/4))). The bound grows faster than every polynomial in b. [Research release and theorem statements](https://github.com/google-research/google-research/tree/master/cogentic_research_papers/deterministic_factoring_l34)

Prime-power coordinate sumsets on modular hyperbolas have an established literature. The surviving-class argument above specializes those local restrictions to a short interval and relates the surviving candidates to the oracle transcripts. No priority claim is made for the modular restrictions. [Bower, Evans, Luo and Miller](https://arxiv.org/abs/1212.2930)

The fast floor-sum recurrence follows by counting lattice points under an affine line from the other axis and applying Euclidean division. [Euclidean floor sums](https://atcoder.jp/contests/practice2/editorial/579)
