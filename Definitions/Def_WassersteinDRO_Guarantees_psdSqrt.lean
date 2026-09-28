import Mathlib

open Classical

namespace WassersteinDRO.Guarantees

/-- The positive-semidefinite square root of a matrix, `Σ^{1/2}`. Redefined locally in this
chapter's own namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def psdSqrt {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  if h : ∃ B : Matrix (Fin m) (Fin m) ℝ, B.PosSemidef ∧ B * B = A then h.choose else 0

end WassersteinDRO.Guarantees
