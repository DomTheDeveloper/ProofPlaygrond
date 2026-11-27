import Lake
open Lake DSL

package «factoring-bit-study»

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib FactoringBitStudy where
  roots := #[`DivisorSumBitReduction, `DoublingWindow, `LocalBitCertificates, `SemiprimeBridge]
