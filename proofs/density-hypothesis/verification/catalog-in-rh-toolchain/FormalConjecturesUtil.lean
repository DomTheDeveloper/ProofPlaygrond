module

public import Mathlib
public import FormalConjecturesForMathlib.NumberTheory.RiemannZetaZeros
public import FormalConjecturesUtil.Attributes.Basic

/-!
REDUCED stand-in for `FormalConjecturesUtil.lean` of google-deepmind/formal-conjectures.

The catalog's own file also imports the rest of `FormalConjecturesForMathlib` and the catalog's
linters. This stand-in imports only what `FormalConjectures/Wikipedia/DensityHypothesis.lean`
needs: Mathlib, the catalog's `RiemannZetaZeros.lean` (the definition of `Complex.zeroCountOn`),
and the catalog's `category` / `AMS` attributes. Those three catalog files are used unmodified.
-/
