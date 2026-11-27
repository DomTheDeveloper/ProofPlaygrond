# Two initial blocks for OEIS A079727

Peter Bala conjectured that a squarefree product of primes congruent to 3, 5, or 6 modulo 7 has its square dividing the sum of the cubed central binomial coefficients through index (n−1)/2. This directory formalizes a two-block proof of the squarefree-product assertion in Lean 4.33.1.

## Mathematical contribution

The theorem `Bala79727.block_lift` works at **every odd prime** p. For any fixed offset r < p, divisibility of the two sums starting at 0 and p by p² implies divisibility of the corresponding sum starting at jp for every j. Its proof clears a common denominator, proves that the resulting numerator is affine in j modulo p², and cancels the denominator. Lucas’s theorem removes the upper half of a block. Coprimality then combines the prime squares.

`Bala79727.squarefree_small` proves the claim for all subsets of the eligible primes below 300 directly from finite arithmetic and the lifting theorem. There are 33 such primes and hence 8,589,934,592 subsets.

`Bala79727.conjecture4` handles every eligible prime. For the two initial half-blocks at primes exceeding 3 it specializes two lemmas in eliayousf’s earlier formalization, `prime_square_eval_zero` and `all_half_blocks_of_eval_zero`, at block indices 0 and 1. It checks the two initial blocks at 3 directly. The remaining steps use the lifting theorem above. The earlier formalization also proves all the higher blocks directly.

## Verification

Run `bash verify.sh` with Git and Elan installed. The script starts in a temporary directory, fetches the pinned prior proof, checks its Git blob hash, and builds the Lean modules against the pinned DeepMind catalogue. The final file checks its theorem against `type_of% @OeisA79727.conjecture4` and prints its axioms.

## Attribution

Peter Bala posed the conjecture in 2024. @domthedeveloper reports independently discovering a proof. The two-block formalization here was developed with OpenAI Codex. The earlier complete Lean proof is by GitHub contributor **eliayousf** using Codex. The present route reuses that contributor’s prime-field results. The formalization here makes no claim of priority over the earlier submission.

- [Bala’s conjecture in OEIS A079727](https://oeis.org/A079727)
- [Google DeepMind’s exact declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/OEIS/79727.lean)
- [Earlier merged proof and its attribution](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6929)
- [Earlier proof’s kernel and axiom audit](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/46009326002/job/140540488330)
- [Zhi-Hong Sun’s initial half-block theorem](https://arxiv.org/pdf/1012.3898)
