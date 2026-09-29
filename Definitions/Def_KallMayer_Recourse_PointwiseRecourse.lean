import Mathlib
import Definitions.Def_KallMayer_Recourse_LPValue

namespace KallMayer.Recourse

/-- Local provisional adapter for the pointwise recourse value in Kall–Mayer,
Chapter 3, (2.4)/(2.9), PDF209/213, and Theorem 2.2, PDF216 (printed207).
This composes the existing book-local LPValue with the residual h - T x;
it does not introduce a probability distribution or take an expectation.
The underlying LPValue and this wrapper are not claimed as published objects. -/
noncomputable def PointwiseRecourse {n₁ n₂ m : ℕ}
    (W : Matrix (Fin m) (Fin n₂) ℝ)
    (T : Matrix (Fin m) (Fin n₁) ℝ)
    (h : Fin m → ℝ) (q : Fin n₂ → ℝ) (x : Fin n₁ → ℝ) : EReal :=
  LPValue W q (h - Matrix.mulVec T x)

end KallMayer.Recourse
