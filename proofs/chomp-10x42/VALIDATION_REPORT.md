# Validation report: 10×42 Chomp three-opening computation

## Verdict

- **Original archive as submitted: fails validation.** Its included C++ source uses uninitialized memory in `Solver::process_prefix()`.
- **Claim after the minimal correction: passes computational validation.** A corrected exact run reproduces the three claimed P-children of the 10×42 rectangle.
- This is an exact retrograde computation, **not** a Lean/kernel proof and not a standalone proof certificate.

## Critical defect in the submitted source

The original code declares

```cpp
uint64_t base[64];
```

and fills only `base[0]` through `base[K-3]`, but the subsequent loop reads through `base[K-2]`. For `K = 10`, `base[8]` is uninitialized.

MemorySanitizer reports a use of an uninitialized value at the call to `Bits::get()`. With GCC 14.2.0 at `-O3`, the original executable could segfault immediately on `10 42`.

The minimal correction is:

```cpp
uint64_t base[64];
base[K - 2] = 0;
uint64_t acc = 0;
```

This is the correct base rank for the one-coordinate final suffix before adding the candidate bottom-row value.

## Checks performed

1. Archive path-safety inspection and source review.
2. Strict GCC build with warnings enabled.
3. AddressSanitizer/UndefinedBehaviorSanitizer small-board run.
4. MemorySanitizer diagnosis of the original defect.
5. Published 6×13 regression reproduced exactly.
6. Independent naive retrograde enumeration on complete small state spaces: 2×8, 3×8, 4×8, 5×8, and 6×7. The corrected solver produced the same ordered list of every P-position and the same rectangle children.
7. Corrected full 10×42 exact runs completed successfully in both scalar and 64-bit bit-window final-row scans; their complete outputs were byte-for-byte identical.

## Fresh corrected 10×42 result

```text
10x42 openings=3
  (42,42,42,42,35,35,35,35,35,35)
  (42,42,42,42,42,42,29,29,29,29)
  (42,42,42,42,42,42,42,25,25,25)
max=3 P=107342138 prefixes=3042311754
```

Runtimes in the validation environment:

```text
bit-window: TIME 2:31.16 RSS 452472KB EXIT 0
scalar:     TIME 3:37.21 RSS 452408KB EXIT 0
```

The three children correspond to opening moves row 5/column 36, row 7/column 30, and row 8/column 26, equivalently bites 7×6, 13×4, and 17×3.

The run proves **at least three** winning openings. It stops immediately upon finding the third, so it does not establish that 10×42 has exactly three winning openings or list every winning opening. That is sufficient for the stated computational challenge.

## Documentation issues in the original archive

The stored primary run named a different executable and input from the included source. Its wording also did not match the source's output. Those stored logs therefore were not treated as reproducibility evidence.

The original package also omitted the source of its claimed independent scalar implementation. The corrected validation performed and recorded fresh complete runs itself.

## Formal verification boundary

The computation is exact and deterministic, but the full 107,342,138-position classification has not been converted into a compact independently checkable certificate or a Lean-kernel derivation. The companion Lean file can formalize the game, legal moves, distinctness, and reduction to the three P-position facts; those three facts remain backed by this external computation.
