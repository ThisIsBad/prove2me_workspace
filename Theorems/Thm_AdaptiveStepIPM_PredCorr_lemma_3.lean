import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 3, printed p. 7, in its equivalent one-iteration invariant form. -/
theorem lemma_3 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hstep : Alg1Step A b c x s xNext sNext) :
    N2 A b c (1 / 4) xNext sNext := by sorry

end AdaptiveStepIPM.PredCorr

