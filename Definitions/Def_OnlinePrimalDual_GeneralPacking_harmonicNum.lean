import Mathlib

namespace OnlinePrimalDual.GeneralPacking

/-- The `n`-th harmonic number `H(n) = ∑_{i=1}^n 1/i` (Buchbinder & Naor, FnT TCS 2009,
Lemma 14.2, p. 251), restated locally in this chunk's own sub-namespace since concurrent draft
missions in this series cannot import each other's definitions (`13-bounded-allocation` also
defines this quantity, for its own Lemma 13.2). -/
noncomputable def harmonicNum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, 1 / (i : ℝ)

end OnlinePrimalDual.GeneralPacking
