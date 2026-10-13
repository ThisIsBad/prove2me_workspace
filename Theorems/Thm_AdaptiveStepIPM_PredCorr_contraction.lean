import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

namespace AdaptiveStepIPM.PredCorr

/-- The contraction displayed in the proof of Theorem 1, printed p. 9. -/
theorem contraction {m n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hstep : Alg1Step A b c x s xNext sNext) :
    mu xNext sNext ≤
      (1 - (8 : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))) * mu x s := by sorry

end AdaptiveStepIPM.PredCorr

