import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 2(a), printed p. 5. -/
theorem lemma_2a {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s : Fin n → ℝ) (hxs : F0 A b c x s) :
    (l2Norm (scaledR x s 0)) ^ 2 = (n : ℝ) * mu x s := by sorry

end AdaptiveStepIPM.PredCorr

