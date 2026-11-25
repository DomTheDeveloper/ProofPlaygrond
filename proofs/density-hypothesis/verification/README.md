# Verification record

Everything here was run on 2026-11-25 (UTC) in one container: 4 CPU cores, 16 GB of memory (a
13.3 GiB limit shared by all commands), about 70 GB of disk. That is far too small for the official
check of the Riemann Hypothesis proof, so the unconditional theorem was verified in a different way,
described in full below. Read section 7 for what this does **not** establish.

| | |
|---|---|
| Proof of RH | [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at commit `fcb6eac7534875d32d68030967e2deae6d686151` (2026-11-25 02:41 UTC; `main` has moved on since) |
| Its toolchain | Lean `v4.37.0-rc1` (`0b77e12`), Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` |
| Catalog | [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, on Lean `v4.33.1`, Mathlib `v4.33.1` |

## 1. What was checked, in one table

| Claim | How it was checked here | Result |
|---|---|---|
| `RiemannHypothesis →` the catalog's Density Hypothesis statement, and the unconditional bound `N(1/2, T) ≤ C T log T` (Mathlib only) | `lake build` on Lean 4.33.1; in situ against the unmodified catalog module (`InSitu.lean`); on Lean 4.37.0-rc1: `lake comparator` (Lean kernel, Lean paranoid kernel, nanoda), `con-leche`, `con-ron`, `leanchecker` | all accept (sections 2, 3) |
| The copied definitions and the statements are the catalog's | structural comparison of the compiled constants on both toolchains; `type_of%` against the catalog's own file | identical (section 4) |
| The Density Hypothesis with no hypothesis | `DensityHypothesis/Unconditional.lean` and `InSituUnconditional.lean` compiled against the compiled module `Main` of the RH proof | compile; axioms `propext`, `Classical.choice`, `Quot.sound` (section 5) |
| ... and it really rests on nothing else | a scan of every constant of all 71,602 compiled modules involved (section 6.2), and a replay of every one of them through Lean's kernel, module by module (section 6.3) | see section 6 |

## 2. The Mathlib-only part on the catalog's toolchain (Lean 4.33.1)

In this directory, with Mathlib `v4.33.1` built:

```text
$ lake build DensityHypothesis Challenge Solution
⚠ [3793/3801] Built Challenge (5.4s)
warning: Challenge.lean:102:8: declaration uses `sorry`
warning: Challenge.lean:109:8: declaration uses `sorry`
warning: Challenge.lean:116:8: declaration uses `sorry`
✔ [3795/3801] Built DensityHypothesis.Defs (5.7s)
✔ [3796/3801] Built DensityHypothesis.ZeroCount (7.2s)
✔ [3797/3801] Built DensityHypothesis.Main (1.6s)
✔ [3798/3801] Built DensityHypothesis (1.4s)
✔ [3800/3801] Built Solution (1.4s)
Build completed successfully (3801 jobs).

$ lake env lean DensityHypothesis/Audit.lean
'DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.zetaZeroCount_half_le_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three warnings are the statements of `Challenge.lean`, whose proofs are left out on purpose.

In a checkout of the catalog at `9097e2f`, with nothing modified, after
`lake build FormalConjectures.Wikipedia.DensityHypothesis`:

```text
$ lake env lean /path/to/proofs/density-hypothesis/InSitu.lean
'DensityHypothesis.density_hypothesis_zeta_zeros_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesis.guth_maynard_zero_density_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DensityHypothesisProof.zeroCountOn_strip_le_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`InSitu.lean` is a `module` that imports the catalog's module and states its two theorems as
`(hRH : RiemannHypothesis) : type_of% @density_hypothesis_zeta_zeros` and
`… : type_of% @guth_maynard_zero_density`: Lean takes the statements from the catalog's own
declarations.

## 3. The Mathlib-only part with Comparator and three more kernels (Lean 4.37.0-rc1)

The Lean release that the RH proof uses ships `lake comparator`, the exporter `leanexport`, and the
checkers `leanchecker`, `leanchecker-paranoid`, `nanoda_bin`, `con-leche` and `con-ron`.
`tools/build_437.sh` compiles this project's files with that release and `tools/check_new_part.sh`
runs the checks; their output is in `results/new-part/`.

`Challenge.lean` states the three theorems with `sorry`, from Mathlib alone; `Solution.lean` is the
library. Both were exported with `leanexport` (the targets are in `export-targets.txt`) and judged
from the exports:

```text
$ lake comparator --config comparator.json --challenge-from-export challenge.export --solution-from-export solution.export
Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!

$ con-leche --jobs=2 solution.export
con-leche: accepted 61639 declarations (--verified)

$ con-ron --jobs=2 solution.export
con-ron: accepted 61639 declarations (--verified)

$ leanchecker DensityHypothesis.Defs DensityHypothesis.ZeroCount DensityHypothesis.Main     # exit code 0
```

Comparator establishes that the three theorems of the solution have the statements of the
challenge, that they use no axiom other than `propext`, `Quot.sound` and `Classical.choice`, and that
the kernels accept the 61,639 declarations they depend on. It was run from exports
(`--challenge-from-export`, `--solution-from-export`), as root, in a container: the sandboxed
build that Comparator normally does itself was replaced by `build_437.sh`. The export files are not
kept (0.8 GB); their SHA-256 are in `results/new-part/exports.txt`, and compiling twice gave
byte-identical `.olean` files and exports.

The bundled `lean4lean` could not read these `.olean` files ("incompatible header") and was not used.

**This covers the implication, not the Riemann Hypothesis.** Comparator on the unconditional
theorem needs an export of the whole RH proof; see section 7.

## 4. Are the statements the catalog's?

`tools/Compare.lean` reads compiled modules and compares constants of the same name structurally
(`==` on kernel terms: equal up to the names of bound variables), including every instance argument.
`results/new-part/statement-comparison.txt` has the full output; in summary:

* **Lean 4.33.1.** The eight declarations of `DensityHypothesis/Defs.lean` are identical, in type
  and in value, to the catalog's own compiled `Complex.zeroCountOn`,
  `DensityHypothesis.zetaZeroCount` and their lemmas. (Before this project used Lean's module
  system they were only definitionally equal.)
* **Lean 4.37.0-rc1.** The catalog itself does not build there, but four of its files compile
  unmodified: `FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean`, the two attribute
  files `FormalConjecturesUtil/Attributes/{AMS,Basic}.lean`, and
  `FormalConjectures/Wikipedia/DensityHypothesis.lean`, the last one against a reduced stand-in for
  `FormalConjecturesUtil.lean` (`catalog-in-rh-toolchain/FormalConjecturesUtil.lean`: Mathlib, the
  definitions file and the attributes, without the rest of the catalog's library and its linters).
  Against those:
  * `DensityHypothesis.density_hypothesis_zeta_zeros` and `guth_maynard_zero_density` of
    `DensityHypothesis/Unconditional.lean` have the same name and identical type as the catalog's
    theorems, and every definition they mention is identical; only the proofs differ (`sorry` there);
  * `InSituUnconditional.lean` imports the catalog's file and proves
    `type_of% @density_hypothesis_zeta_zeros` and `type_of% @guth_maynard_zero_density` with no
    hypothesis;
  * `comparator/CatalogChallenge.lean` (the two statements with the catalog's attributes removed)
    is identical to the catalog's file on every shared constant.

## 5. Composition with the compiled proof of RH

The RH proof was **not recompiled** (that takes hours on a far larger machine). Its compiled
modules were taken from the project's build cache:

* the cache's receipt for commit `fcb6eac` (`results/rh-cache-receipt.json`) reports
  `build_exit_code 0`; its `candidate_tree`, `source_tree`, lakefile and manifest hashes equal those
  of the git checkout at that commit;
* all 59,763 artifacts named by the receipt's module manifest were downloaded (3.63 GB) and each one
  matched the manifest's SHA-256 (`tools/fetch_artifacts.py`);
* Mathlib's own cache was fetched separately
  (`MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get`).

The cache's own documentation says that it does not verify proofs. Nothing below relies on it for
that: the compiled declarations themselves are re-checked in section 6.

Every module of the RH proof is a Lean `module` and has three files: `X.olean` (the public part, in
which a theorem appears as an axiom with its statement), `X.olean.server`, and `X.olean.private`
(everything, with the proofs). Unpacked they take 70 GB, so only the public parts (10 GB) are kept
on disk, and the private parts are unpacked again a few thousand modules at a time when they are
read.

`DensityHypothesis/Unconditional.lean` is

```lean
module

public import DensityHypothesis.Main
import Main

theorem density_hypothesis_zeta_zeros (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) :=
  density_hypothesis_zeta_zeros_of_riemannHypothesis riemannHypothesis ε hε
```

(in the namespace `DensityHypothesis`; `Main` is the RH repository's module that declares
`theorem riemannHypothesis : RiemannHypothesis`). It compiles against the public parts, which is all
a `module` needs from its imports (`lean --setup`, written by `tools/mksetup.py`):

```text
'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'DensityHypothesis.density_hypothesis_zeta_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
'DensityHypothesis.guth_maynard_zero_density' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and so does `InSituUnconditional.lean` (section 4):

```text
'DensityHypothesis.density_hypothesis_zeta_zeros_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'DensityHypothesis.guth_maynard_zero_density_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two things this output does **not** show. In this Lean release `#print axioms` does not walk the
proofs of imported theorems: it reads a list that was stored in each `.olean` when that file was
compiled (`Lean/Util/CollectAxioms.lean`). And compiling against public parts type-checks only the
new file. Section 6 addresses both.

## 6. Re-checking the compiled proof of RH on this machine

### 6.1 Why not the official way

The RH repository's own check is `lake comparator`: export the whole proof with `leanexport`
(about 60 GB) and run the kernels on the export. That needs a machine with hundreds of GB of memory
and was done by that project, not here. What follows uses Lean's kernel through its API, in tools
written for this purpose (`tools/Scan.lean`, `tools/Replay.lean`, with the drivers `tools/pass1.py`
and `tools/pass2.py`). They are not standard tools and have had one adversarial review
(`results/audit.md`), not years of use.

### 6.2 Scan: what does the theorem depend on?

`Scan.lean` reads the three parts of a module with Lean's `readModuleDataParts` and writes, for
every constant of the most private part, its kind (axiom, theorem, definition, ...) and the
constants its type, value, constructors or recursor rules mention; it also checks that every
constant of the public part is a view of the private one (same type and universe parameters, body
hidden or identical). `analyze.py` joins the 71,602 records and follows references from a root,
inside the import closure of the root's module, taking **every** declaration of a name when
several modules declare it.

| Root (declared in) | Modules in its import closure | Declarations reachable | Axioms reached |
|---|---|---|---|
| `riemannHypothesis` (`Main`) | 70,913 | 1,410,928 (1,185,834 theorems, 207,956 definitions) | `Classical.choice`, `Quot.sound`, `propext` |
| `DensityHypothesis.density_hypothesis_zeta_zeros` (`DensityHypothesis.Unconditional`) | 70,917 | 1,411,007 (1,185,904 theorems, 207,965 definitions) | `Classical.choice`, `Quot.sound`, `propext` |
| `DensityHypothesis.guth_maynard_zero_density` (`DensityHypothesis.Unconditional`) | 70,917 | 1,411,008 (1,185,905 theorems, 207,965 definitions) | `Classical.choice`, `Quot.sound`, `propext` |
| `DensityHypothesis.zetaZeroCount_half_le_mul_log` (`DensityHypothesis.Main`) | 5,749 | 63,061 (49,146 theorems, 11,521 definitions) | `Classical.choice`, `Quot.sound`, `propext` |
| `DensityHypothesis.density_hypothesis_zeta_zeros_proved` (`InSituUnconditional`) | 71,352 | 1,411,006 (1,185,903 theorems, 207,965 definitions) | `Classical.choice`, `Quot.sound`, `propext` |
| `DensityHypothesis.guth_maynard_zero_density_proved` (`InSituUnconditional`) | 71,352 | 1,411,007 (1,185,904 theorems, 207,965 definitions) | `Classical.choice`, `Quot.sound`, `propext` |
| `DensityHypothesis.density_hypothesis_zeta_zeros` (`FormalConjectures.Wikipedia.DensityHypothesis`) | 11,628 | 53,637 (41,005 theorems, 10,346 definitions) | `Classical.choice`, `Quot.sound`, `propext`, `sorryAx` |

Over the 59,763 modules of the RH proof's build: 1,429,808 constants
(1,179,017 theorems, 231,253 definitions, 6,434 inductive types with
6,670 constructors and 6,434 recursors), **0 axioms**, 0 opaque constants.
All 1,092,268 constants of their public parts are views of the private ones.
Across all 71,602 modules scanned, 91 axioms are declared, all in Lean core, Lake or Mathlib's
dependencies. No reachable declaration is unsafe or partial, none refers to a name that is not declared, and
no declaration anywhere refers to a constant that is only declared in a later module
(`references_to_later_modules = 0`). 9,897 names are declared by more than one
module; almost all are auto-generated equation and congruence theorems.

So no axiom is declared anywhere in the RH proof's modules, and what the unconditional theorem
reaches in Lean core and Mathlib are the three standard axioms. As a control, the same analysis
applied to the catalog's own `sorry`-ed `density_hypothesis_zeta_zeros` reports `sorryAx`.

### 6.3 Replay: is every one of those declarations accepted by the kernel?

`Replay.lean` processes modules in a topological order of the import graph and keeps one kernel
environment `E`.

* For each module, **every constant of its most private part is sent to Lean's kernel**
  (`Kernel.Environment.addDeclCore`, full type checking, the function `leanchecker` uses) on top of
  `E`, in dependency order. The public part is compared with the private part as in 6.2.
* Then the module's public part is inserted into `E` as it is, which is what importing the module
  does. For the five modules of the RH proof that another module imports with `import all`, the
  private part is inserted instead.
* So each module's proofs are checked against the public views of **earlier** modules only: a
  theorem of an earlier module is available as a statement, exactly as it was when the module was
  compiled, and nothing is checked against anything that comes later.
* Lean lets several modules declare the same auto-generated theorem (`f.eq_1`, `f.congr_simp`, ...).
  When a module's theorem meets a copy already in `E`, the copy must have the same type and universe
  parameters, and the module's own proof is still checked in full, under a fresh name. A definition
  that meets a copy must be identical to it. Anything else is an error.
* Unsafe and partial definitions (compiler helpers such as `f._unsafe_rec`) are skipped, as in
  `leanchecker`; the kernel does not let a theorem or a safe definition refer to them.

If every module passes, the constants of all private parts, added in that order, form an
environment in which every theorem has a proof that the kernel has checked: replacing the statement
of an earlier theorem (or the signature of a definition whose body was hidden) by the full
declaration of the same type does not invalidate a typing derivation. This is an argument about the
type theory. It is weaker than what the official check does, which is to run the kernels once over
the whole environment at the same time.

Three runs, with the driver `pass2.py` (results in `results/replay-*/`):

| Run | Modules | Accepted | Rejected | Constants | Sent to the kernel | Duplicate theorems re-checked | Kernel time |
|---|---|---|---|---|---|---|---|
| RH proof: the 59,723 modules of the RH proof that `Main` imports, then the four modules of this project; Lean core and Mathlib imported as they are | not finished | | | | | | |
| this project: the modules of this project as built from this repository by `build_437.sh`, on top of the public views of the RH proof | 6 | 6 | 0 | 72 | 72 | 0 | 0.0 CPU-hours |
| in situ: the catalog's four files, the stand-in, and `InSituUnconditional`, on top of the public views of the RH proof | 6 | 6 | 0 | 661 | 563 | 0 | 0.0 CPU-hours |
| Lean core and Mathlib: the 11,623 modules of Lean core, Mathlib and its dependencies in the import closure, from an empty environment | not finished | | | | | | |

(The table is regenerated when the runs finish; a run marked "not finished" was still going when this was written.)

Controls, run with the same binary (`results/controls.txt`):

* `controls/Bogus.lean` declares `Bogus.falseHolds : False` with the proof term `True.intro`, added
  with the kernel switched off (`debug.skipKernelTC`), so that Lean compiles the file. The replay
  rejects it: `(kernel) declaration type mismatch, 'Bogus.falseHolds' has type True but it is
  expected to have type False`.
* A module of the RH proof fed before the modules it depends on is rejected
  (`(kernel) unknown constant`), and accepted in its place in the order.

**Tool revisions.** The replay tool changed twice while the main run was going, each time between rounds of the driver. Revision 1 (interpreted; the file was edited in place afterwards and only its SHA-256 is kept, in `results/replay-rh/tool_revisions.txt`): the first 8,114 modules. It rejected one further module because of an over-strict rule for the public view of an unsafe helper definition; that module passed under the corrected rule. Revision A (`tools/history/Replay.revA.lean`, native): up to module 23,298 of the order. Revision B (`tools/Replay.lean`): everything after that, the other three runs and all controls. A and B differ only in how a public view is put into the environment: A handed it to the kernel with checking switched off (`addDeclWithoutChecking`), which fails for the few public views that mention a private name they do not contain; B inserts the constants directly, as Lean's own import does. The code that checks a module's private part is the same in all three.

## 7. What this does not establish

* **The official check of the unconditional theorem was not run.** `comparator/catalog.json` and
  `comparator/CatalogChallenge.lean` are the inputs `lake comparator` would need
  (challenge: the catalog's two statements; solution: `DensityHypothesis.Unconditional`). Nobody has
  run them. On a machine that can check the RH proof itself, this adds four small modules to it.
* **No independent kernel was run on the RH proof here.** `nanoda`, `con-leche`, `con-ron` and the
  paranoid kernel saw only the Mathlib-only part (section 3). For the RH proof, section 6 uses the
  one kernel that ships with Lean. That the RH proof passes the other kernels is the RH project's
  result (its `verification/NOTES.md`), not something reproduced here.
* **The RH proof was not rebuilt from its sources.** The compiled modules come from the project's
  cache for commit `fcb6eac`. What was re-checked is that those compiled declarations are accepted
  by the kernel and contain `riemannHypothesis : RiemannHypothesis` with Mathlib's
  `RiemannHypothesis`; that the 59,763 source files compile to them was not.
* **Custom tools.** The replay is module by module with tools written during this work; see 6.1 and
  the argument in 6.3.
* **Trust that remains in any case:** Lean's kernel and the correctness of its implementation, the
  three axioms, and that Mathlib's `RiemannHypothesis`, `riemannZeta` and the catalog's
  `zetaZeroCount` say what they are meant to say.

## 8. Reproducing

All paths are examples. `lean`, `lake` and the other binaries are those of Lean `v4.37.0-rc1` unless
stated.

```bash
git clone https://github.com/leanprover-community/riemann-hypothesis rh
```

```bash
cd rh && git checkout fcb6eac7534875d32d68030967e2deae6d686151 && MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
```

Fetch `ci/revisions/fcb6eac7534875d32d68030967e2deae6d686151.json` and the module manifest it names
from `https://rh-cache.taucetiproject.org`, make a JSON map from artifact file name to SHA-256 out of
the manifest, then:

```bash
python3 verification/tools/fetch_artifacts.py sha256.json rh/.lake/cache/artifacts
```

```bash
python3 verification/tools/pass1.py modules.jsonl.gz rh/.lake/cache/artifacts rh/.lake/build scan/ "$(dirname "$(which lean)")" verification/tools/Scan.lean
```

```bash
verification/tools/build_437.sh . rh /path/to/formal-conjectures out/
```

```bash
verification/tools/check_new_part.sh . rh out/ results/
```

```bash
python3 verification/tools/analyze.py analysis/ riemannHypothesis,DensityHypothesis.density_hypothesis_zeta_zeros scan/ scan_ext/ scan_dh/
```

```bash
cd verification/tools && lake build rhreplay
```

```bash
python3 verification/tools/pass2.py cfg.json
```

`scan_ext/` and `scan_dh/` are scans of Mathlib, Lean core and this project's modules made with
`lean --run verification/tools/Scan.lean <list> <out>`. The configurations that were used for
`pass2.py` are in `results/` (`cfg_*.json`, with this machine's paths); the keys are documented at
the top of `pass2.py`. The replay of the RH proof took about (to be filled in) on four cores.
