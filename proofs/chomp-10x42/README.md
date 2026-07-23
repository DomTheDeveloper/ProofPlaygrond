# A 10 by 42 Chomp rectangle with three winning openings

## Result

The OEIS-linked challenge asks for a rectangular Chomp board with at least three winning first moves. A solution is the **10 by 42** rectangle.

Using rows numbered from top to bottom and columns from left to right, the following three opening moves are winning:

1. **row 5, column 36**;
2. **row 7, column 30**;
3. **row 8, column 26**.

Equivalently, in the “width removed by height removed” bite notation used by Ekhad and Zeilberger, the three bites are

\[
7\times 6,\qquad 13\times 4,\qquad 17\times 3.
\]

They leave, respectively, the three Ferrers positions

\[
(42,42,42,42,35,35,35,35,35,35),
\]

\[
(42,42,42,42,42,42,29,29,29,29),
\]

and

\[
(42,42,42,42,42,42,42,25,25,25).
\]

The exact retrograde computation classifies all three as P-positions, so moving to any one of them is a winning opening.

## Position convention

A position on a board with `K` rows and maximum width `N` is represented by a nonincreasing vector

\[
x=(x_0,x_1,\ldots,x_{K-1}),\qquad N\ge x_0\ge x_1\ge\cdots\ge x_{K-1}\ge0.
\]

A move in row `i` that leaves `t` squares in that row sends `x` to `y`, where

\[
y_j=x_j\quad(j<i),\qquad y_j=\min(x_j,t)\quad(j\ge i).
\]

The poisoned square is treated as unavailable. Thus the position containing only the poisoned square has no legal move and is a P-position.

## Why the algorithm is exact

The program enumerates positions lexicographically with every coordinate increasing subject to the partition inequalities. Every legal move strictly decreases the first coordinate at which the source and target differ, so every option has already been classified.

A position is an N-position exactly when it has an option that is a previously found P-position. Rather than storing every classified position, the program stores, for each possible move row, the exact *shadow* of all previously found P-positions: the suffixes of later positions that can move to one of those P-positions in that row. The shadow characterization follows directly from the formula `y_j = min(x_j,t)` above. Therefore:

- membership in any shadow means that a move to a P-position exists, so the current position is N;
- absence from every shadow means that no move to a P-position exists, so the current position is P.

There is also an exact dimension reduction. Once the first `K-1` row lengths are fixed, at most one final-row length can give a P-position. Indeed, if two did, the position with the larger final row could move directly to the one with the smaller final row, contradicting that both are P. The solver therefore tests final-row lengths in increasing order and stops after the first P-position.

These observations prove that the program performs complete retrograde analysis; no random search, heuristic evaluation, or unproved periodicity assumption is used.

## Certificate output

The exact run for `10 42` reports:

```text
10x42 openings=3
  (42,42,42,42,35,35,35,35,35,35)
  (42,42,42,42,42,42,29,29,29,29)
  (42,42,42,42,42,42,42,25,25,25)
max=3 P=107342138 prefixes=3042311754
```

The executable stops immediately after the third P-child of the 10 by 42 rectangle is found. Before that point it has processed 3,042,311,754 fixed-prefix cases and identified 107,342,138 P-positions.

## Reproduction

Compile and run:

```bash
g++ -O3 -march=native -DNDEBUG chomp_three_openings.cpp -o chomp
./chomp 10 42
```

As a small published-data check, running `./chomp 6 13` returns the two known losing children

```text
(13,13,13,11,11,11)
(13,13,13,13,8,8)
```

corresponding to the two known winning bites of the 6 by 13 rectangle.

## Verification status

- The source SHA-256 is `fe8ec31248ca85cb10e182c2518f3a14ab4a5e8d6fc6145ba489ceafc84a32fd`.
- The uploaded package records two exact implementations producing the same `10 × 42` result.
- A fresh rebuild in the proof sandbox reproduced the published `6 × 13` regression exactly.
- The full `10 × 42` run requires more memory than the current proof sandbox provides; the recorded full outputs are preserved in `verification.txt`.
- This is an exact computational proof package, not yet a kernel-checked Lean certificate. The corresponding Formal Conjectures file formalizes the statement without pretending that the C++ computation has been checked by Lean.

## Status and references

This supplies the requested mathematical witness for the second computational challenge. Award or public acknowledgment of the pledged donation remains subject to independent verification by the problem proposer.

- OEIS A147983: https://oeis.org/A147983
- S. B. Ekhad and D. Zeilberger, “All the Winning Bites for a by b Chomp for a and b up to 14 and Two Computational Challenges”: https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/chompc.html
