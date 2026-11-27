# Which stone-pile positions are reachable?

Start with $n\ge1$ piles, each holding one stone. A move transfers any positive number of stones between two piles that start at the same size. An emptied pile disappears. A position is an unordered partition of $n$. A terminal position has distinct parts.

Let $P(n)$ count all partitions and $Q(n)$ count partitions into distinct parts. Let $U(n)$ count unreachable positions and $T(n)$ count unreachable terminal positions. Thus $U(n)$ is A292727 and $Q(n)-T(n)$ is A292728.

For every odd prime $p$, Charlie Neder's two proposed counts hold:

$$
U(4p)=p+4,\qquad U(8p)=2p+20.
$$

The two terminal-state conjectures in Peter Kagey's sequence hold as well. Every terminal position is reachable exactly when $n$ is a power of two. Exactly one terminal position is unreachable precisely when $n$ is an odd prime. [Neder's conjectures](https://oeis.org/A292727) · [Kagey's sequence](https://oeis.org/A292728)

## A test for any position

Let $m$ be the largest odd divisor of $n$. Call a position primitive if its parts have no common odd divisor greater than one.

1. A nonprimitive position is unreachable.
2. A primitive position with an even part or a repeated part is reachable. The singleton $(1)$ is also reachable.
3. A primitive position of distinct odd parts $x_1,\ldots,x_r$, with $r\ge2$, is reachable exactly when some pair $i<j$ satisfies
   $\gcd(m,\,x_k\text{ for }k\notin\{i,j\})=1$. For two parts, the gcd in this test is $m$.

**Proof.** A reverse move splits an even pile in half or replaces two unequal piles of the same parity by two copies of their average. These are exactly the inverses of forward transfers. Each strictly decreases the sum of squares of pile sizes. A common odd divisor survives either operation because division by two preserves divisibility by an odd number.

Suppose a primitive position contains a repeated pile $a$. Split an even pile whenever one is present. This preserves the common odd divisors and creates two equal piles. If all piles are odd and equal, primitivity makes them all ones. Otherwise, average one copy of $a$ with a different pile $b$, retaining another copy of $a$. An odd divisor of every new pile divides $a$ and $(a+b)/2$, so it divides $b$ as well. This preserves primitivity and again creates a repeated pile. Strict descent must end at all ones. A primitive position with an even part enters the same argument by splitting that part.

If all parts are odd and distinct, every first reverse move averages a pair. An odd divisor divides all the resulting piles exactly when it divides $n$ and every untouched pile. This follows by subtracting the untouched parts from $n$ and dividing by two. Averaging creates a repeated pile, so the preceding argument decides whether that first move can lead to all ones.

Gregory Igusa's *On Splitting Up Piles of Stones* (2005), Lemma 3.1 and Theorem 3.2, established the repeated-pile observation and a first-move criterion in a related game allowing arbitrary mergers and equal splits. The proof above uses the OEIS moves directly. In 2019 Neder gave an inverse-move proof for the cases of zero or one missing position among all partitions. [Igusa's paper](https://people.brandeis.edu/~kleinboc/47a/pilesofstones.pdf) · [Neder's argument](https://oeis.org/A292726)

## Counting formulas

In a primitive position of distinct odd parts, an odd prime $p\mid n$ obstructs a pair only if it divides every untouched part. It then divides neither of the chosen parts. If it divided one, it would divide their sum and hence both, contradicting primitivity. The chosen parts must be precisely the two parts not divisible by $p$. **Each prime can therefore obstruct at most one pair.**

If $n$ has at most two distinct odd prime factors and $r\ge3$, one of the at least three pairs is unobstructed. The missing positions are exactly those with a common odd prime divisor together with, for even $n$ with $m>1$, the additional coprime odd two-part positions. These additional positions are the unordered pairs $(a,n-a)$ with $\gcd(a,n)=1$. There are $\varphi(n)/2$ because $a\mapsto n-a$ has no fixed point for these $n$.

For either $B=P$ (all positions) or $B=Q$ (terminal positions), the number with a common odd prime divisor is

$$
C_B(n)=\sum_{\varnothing\ne S\subseteq\{p:p\mid m,\ p\ {\rm prime}\}}
 (-1)^{|S|+1} B\left(n\Big/\prod_{p\in S}p\right).
$$

This follows by inclusion–exclusion, dividing every pile by the specified product. In particular, for $n=2^k p^a$, $p$ an odd prime and $a\ge1$,

$$
U(n)=P(n/p)+\begin{cases}0&k=0,\\ \varphi(n)/2&k\ge1,\end{cases}
\qquad
T(n)=Q(n/p)+\begin{cases}0&k=0,\\ \varphi(n)/2&k\ge1.\end{cases}
$$

For $n=4p$ this gives $5+(p-1)=p+4$. For $n=8p$ it gives $22+2(p-1)=2p+20$. At $n=16p$ it gives the further formula $231+4(p-1)=4p+227$.

For the terminal conjectures, every partition of a power of two passes the test. For an odd prime $p$, the formula gives $T(p)=Q(1)=1$, and the missing position is $(p)$. In every other case choose an odd prime $p\mid n$ and let $h=n/p\ge2$. If $h\ge3$, the singleton $(n)$ and the distinct pair $(p,(h-1)p)$ have a common odd divisor within each position and are both unreachable. If $h=2$, the singleton $(2p)$ and the pair $(1,2p-1)$ are unreachable, since that pair can only be averaged to $(p,p)$. This proves both equivalences. At $n=10$ the three missing terminal positions are $(10),(1,9),(3,7)$. The OEIS example also lists $(5,5)$, which permits a transfer. [Source example](https://oeis.org/A292728)

For **every** positive $n$, the repeated-pile result also gives

$$
\mathrm{A292726}(n)-\mathrm{A292728}(n)
=\sum_{d\mid m}\mu(d)\big(P(n/d)-Q(n/d)\big).
$$

The left side counts reachable positions with a repeated part. Möbius inversion on the right counts the positions with a repeated part and no odd common divisor greater than one.

## The smallest obstructions with at least three piles and no common odd divisor

Such a position must have distinct odd parts. Each of its $\binom r2$ pairs needs a different odd prime divisor of $n$. For odd $n$, the smallest possible length is three and therefore $n\ge3\cdot5\cdot7=105$. This is attained by $(3,25,77)$. Averaging 3 and 25 leaves multiples of 7. Averaging 3 and 77 leaves multiples of 5. Averaging 25 and 77 leaves multiples of 3.

For even $n$, the number of odd parts is even, so at least four piles and six distinct odd primes are necessary. Thus $n\ge 2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17=510510$. This is attained by

$$
(2431,\ 2975,\ 17199,\ 487905).
$$

These four numbers have gcd 1. For their six pairs in lexicographic order, the gcds in the reachability test are $3,5,7,11,13,17$. The bounds concern positions with at least three piles. Coprime two-pile obstructions already occur at six stones.

## Verification

Run the accompanying Python checker. A breadth-first search builds the game using only forward transfers. Separately, the checker enumerates every partition and applies the arithmetic test. The two results agree for all 313,064 partitions with totals 1 through 42. The checker also verifies the six exceptional triples at 105, giving $U(105)=15,833$ and $T(105)=685$, and the six pair obstructions at 510,510.

### Lean verification

The Lean file formalizes positive pile sizes as finite multisets, the two inverse transfers, and reachability by any finite number of moves. Theorem `StonePiles.reachable_iff` proves the one-move criterion for every positive position. Theorem `StonePiles.reachable_of_single_odd_prime` proves that if the total has no odd prime factor other than $p$, then a position with at least three piles is reachable whenever some pile is not divisible by $p$. These are the structural theorems used in the counting proof. The partition counts and minimality arguments above are written proofs.

This directory is a standalone Lake project pinned to Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. From this directory run

```sh
lake update
lake exe cache get Mathlib/Algebra/BigOperators/Group/Multiset/Basic.lean Mathlib/Data/Nat/Prime/Basic.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/Push.lean
lake env lean StonePiles.lean
```

Both theorems compiled with the default Lean kernel. Their axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.
