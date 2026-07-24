/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Arxiv.«2508.10245».Geode5
import Mathlib.Data.Nat.ChineseRemainder

/-!
# CRT certificate layer for the five-dimensional Geode computation

This module formalizes the exact Chinese-remainder and uniqueness layer from the
computational certificate for `G(1000,1000,1000,1000,1000)`.

It deliberately separates the already-checkable arithmetic certificate from the
remaining mathematical bridge: proving that the five-state moment recurrence
computes `geode5Diagonal`.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped Function

private def parseNat (s : String) : ℕ :=
  s.trim.toNat?.getD 0

private def parsePair (line : String) : ℕ × ℕ :=
  match line.trim.splitOn " " with
  | p :: r :: _ => (parseNat p, parseNat r)
  | _ => (0, 0)

/-- The exact 8,367-digit candidate value from the certificate package. -/
def answerValue : ℕ :=
  parseNat (include_str "data/G5_1000.txt")

/-- The rigorous hyper-Catalan upper bound used in the certificate. -/
def upperBound : ℕ :=
  Nat.factorial 20002 /
    (Nat.factorial 15002 * Nat.factorial 1001 * Nat.factorial 1000 ^ 4)

/-- The 480 `(prime, residue)` pairs used for the CRT reconstruction. -/
def residuePairs : List (ℕ × ℕ) :=
  ((include_str "data/residues_480.txt").trim.splitOn "\n").map parsePair

/-- Product of all 480 moduli. -/
def certificateModulus : ℕ := (residuePairs.map Prod.fst).prod

theorem residuePairs_length : residuePairs.length = 480 := by
  native_decide

/-- The stored moduli are pairwise coprime. -/
theorem residueModuli_pairwise_coprime :
    residuePairs.Pairwise (Nat.Coprime on Prod.fst) := by
  native_decide

/-- Every stored residue is in the canonical interval for its modulus. -/
theorem residueValues_canonical :
    ∀ pr ∈ residuePairs, pr.2 < pr.1 := by
  native_decide

/-- The proposed exact answer has every residue recorded in the ZIP certificate. -/
theorem answer_modEq_residue :
    ∀ pr ∈ residuePairs, answerValue ≡ pr.2 [MOD pr.1] := by
  native_decide

/-- The hyper-Catalan upper bound is strictly below the CRT modulus. -/
theorem upperBound_lt_certificateModulus :
    upperBound < certificateModulus := by
  native_decide

/-- The proposed answer lies below the rigorous upper bound. -/
theorem answerValue_lt_upperBound : answerValue < upperBound := by
  native_decide

/--
Any natural number with the 480 certified residues is congruent to `answerValue`
modulo the product of all 480 moduli.
-/
theorem modEq_answerValue_of_residues (z : ℕ)
    (hz : ∀ pr ∈ residuePairs, z ≡ pr.2 [MOD pr.1]) :
    z ≡ answerValue [MOD certificateModulus] := by
  apply (Nat.modEq_list_map_prod_iff residueModuli_pairwise_coprime).2
  intro pr hpr
  exact (hz pr hpr).trans (answer_modEq_residue pr hpr).symm

/--
CRT uniqueness below the rigorous Geode upper bound.

This is the final arithmetic step of the certificate: once a nonnegative
candidate is proved to satisfy the stored residues and the hyper-Catalan bound,
it must equal the 8,367-digit answer.
-/
theorem eq_answerValue_of_residues_of_lt_upperBound (z : ℕ)
    (hz : ∀ pr ∈ residuePairs, z ≡ pr.2 [MOD pr.1])
    (hzlt : z < upperBound) :
    z = answerValue := by
  exact (modEq_answerValue_of_residues z hz).eq_of_lt_of_lt
    (hzlt.trans upperBound_lt_certificateModulus)
    (answerValue_lt_upperBound.trans upperBound_lt_certificateModulus)

/--
The exact remaining bridge needed to discharge the benchmark theorem from the
ZIP certificate.

The recurrence formalization must supply:
1. nonnegativity of `geode5Diagonal 1000`;
2. the hyper-Catalan upper bound;
3. all 480 modular residue equalities.
-/
theorem geode5_1000_of_certificate
    (hnonneg : 0 ≤ geode5Diagonal 1000)
    (hbound : Int.toNat (geode5Diagonal 1000) < upperBound)
    (hres : ∀ pr ∈ residuePairs,
      Int.toNat (geode5Diagonal 1000) ≡ pr.2 [MOD pr.1]) :
    geode5Diagonal 1000 = (answerValue : ℤ) := by
  have hnat :
      Int.toNat (geode5Diagonal 1000) = answerValue :=
    eq_answerValue_of_residues_of_lt_upperBound _ hres hbound
  calc
    geode5Diagonal 1000 = Int.toNat (geode5Diagonal 1000) := by
      symm
      exact Int.toNat_of_nonneg hnonneg
    _ = answerValue := by exact_mod_cast hnat

#print axioms residueModuli_pairwise_coprime
#print axioms answer_modEq_residue
#print axioms upperBound_lt_certificateModulus
#print axioms geode5_1000_of_certificate

end Arxiv.«2508.10245».Geode5Proof
