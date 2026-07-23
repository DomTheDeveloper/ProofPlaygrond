# A 10 by 42 Chomp rectangle with at least three winning openings

## Result

The Ekhad–Zeilberger computational challenge asks for a rectangular Chomp board with at least three winning first moves. A validated witness is the **10 by 42** rectangle.

Using rows numbered from top to bottom and columns from left to right, the three certified opening moves are:

1. row 5, column 36;
2. row 7, column 30;
3. row 8, column 26.

Equivalently, the bites are `7 × 6`, `13 × 4`, and `17 × 3`. They leave the P-positions

```text
(42,42,42,42,35,35,35,35,35,35)
(42,42,42,42,42,42,29,29,29,29)
(42,42,42,42,42,42,42,25,25,25)
```

The solver stops after finding the third winning opening, so the established claim is **at least three**, not exactly three.

## Important correction

The originally uploaded source was not valid as written. In `Solver::process_prefix()`, it read `base[K - 2]` without initializing it. MemorySanitizer detected the error, and an ordinary optimized build could crash on the full input.

The mathematically correct repair is:

```cpp
uint64_t base[64];
base[K - 2] = 0;
uint64_t acc = 0;
```

The source in this directory includes that correction. Do not use the earlier uncorrected version.

## Fresh validation

The corrected program was rebuilt and checked by:

- strict GCC compilation;
- AddressSanitizer and UndefinedBehaviorSanitizer on small boards;
- MemorySanitizer diagnosis of the original defect;
- exact comparison with an independently written naive retrograde solver on complete state spaces `2×8`, `3×8`, `4×8`, `5×8`, and `6×7`;
- reproduction of the published `6×13` regression;
- two complete corrected `10×42` runs using scalar and 64-bit final-row scans.

Both full runs produced byte-for-byte identical output:

```text
10x42 openings=3
  (42,42,42,42,35,35,35,35,35,35)
  (42,42,42,42,42,42,29,29,29,29)
  (42,42,42,42,42,42,42,25,25,25)
max=3 P=107342138 prefixes=3042311754
```

Recorded runtimes in the validation environment:

```text
bit-window: TIME 2:31.16 RSS 452472KB EXIT 0
scalar:     TIME 3:37.21 RSS 452408KB EXIT 0
```

See `VALIDATION_REPORT.md` for the full audit and exact limitations.

## Reproduction

```bash
g++ -std=c++17 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic \
  chomp_three_openings.cpp -o chomp
./chomp 6 13
./chomp 10 42
```

The optional `chomp_three_openings_fast.cpp` uses the same exact recurrence with a 64-bit final-row scan.

## Formal verification boundary

This package is an exact computational proof, but it is **not** yet a Lean-kernel certificate. The associated Formal Conjectures entry formalizes the game, the three legal moves, and the target theorem. The three large P-position classifications still rely on this external exact computation.

## References

- OEIS A147983
- Shalosh B. Ekhad and Doron Zeilberger, *All the Winning Bites for a by b Chomp for a and b up to 14 and Two Computational Challenges* (2018)
