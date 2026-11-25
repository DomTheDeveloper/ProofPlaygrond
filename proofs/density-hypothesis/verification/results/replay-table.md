| Run | Modules | Accepted | Rejected | Constants | Sent to the kernel | Duplicate theorems re-checked | Kernel time |
|---|---|---|---|---|---|---|---|
| RH proof: the 59,723 modules of the RH proof that `Main` imports, then the four modules of this project; Lean core and Mathlib imported as they are | not finished | | | | | | |
| this project: the modules of this project as built from this repository by `build_437.sh`, on top of the public views of the RH proof | 6 | 6 | 0 | 72 | 72 | 0 | 0.0 CPU-hours |
| in situ: the catalog's four files, the stand-in, and `InSituUnconditional`, on top of the public views of the RH proof | 6 | 6 | 0 | 661 | 563 | 0 | 0.0 CPU-hours |
| Lean core and Mathlib: the 11,623 modules of Lean core, Mathlib and its dependencies in the import closure, from an empty environment | not finished | | | | | | |
