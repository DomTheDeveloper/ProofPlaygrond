# Number-theory proofs and counterexamples

| Problem | Contribution and evidence |
| --- | --- |
| [Sun’s four-square conjecture, OEIS A261876](https://oeis.org/A261876) | For the retained triple (18, 38, 18), all 496,920 ordered representations of 822,335 fail the square test. This also refutes the six-triple universal variant proposed in [Formal Conjectures #8070](https://github.com/google-deepmind/formal-conjectures/pull/8070). A distinct earlier counterexample used a triple removed from Sun’s revision. The Lean exhaustive test uses `native_decide`. The independent standard-library program `check_four_squares.py` verifies the same count with exact integer square roots. |
| [Firoozbakht, A086766](https://oeis.org/A086766) | Every positive number of repetitions of 109890 followed by 1 is composite. Earlier examples already refuted the original claim. This witness also survives the 2022 proposed exclusion. The Lean certificate, target comparison, source, and audit are in `firoozbakht/`. |
| [Sun, A279821](https://oeis.org/A279821) and [Ordowski, A079853](https://oeis.org/A079853) | `TwoConjectures.lean` proves the central-trinomial witness 1,316,632,279 and the inverse-power characterization. The latter also follows from Lerch’s classical congruence. |
| [Noe, A069004](https://oeis.org/A069004) | Written proof that the lower and upper limiting ratios to the prime count are zero and infinity. `A069004Finite.lean` checks a finite product inequality used by the argument. The previously known upper-bound counterexample is discussed in the manuscript. |
| [Wilson, A251758](https://oeis.org/A251758) | A separate argument identifies the least index with value 8 and an infinite family attaining 8. An earlier [upstream proof submission](https://github.com/google-deepmind/formal-conjectures/pull/8297) gives the least index. The archive contains the finite checks for this argument. |

`PostedInteger.lean` is a standalone arithmetic example. It certifies divisibility by 7 of 8193746205841170392658200302327406197. No named conjecture is attached to that example. The supplied research notes and proof development used AI assistance.
