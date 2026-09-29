import Mathlib

namespace KallMayer.Recourse

/-- Complete fixed recourse: every right-hand side has a nonnegative recourse
vector. Kall–Mayer (2005), Chapter 3, equation (2.6), printed p. 201. -/
def CompleteRecourse {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ z : Fin m → ℝ, ∃ y : Fin n → ℝ,
    (∀ j, 0 ≤ y j) ∧ Matrix.mulVec W y = z

end KallMayer.Recourse
