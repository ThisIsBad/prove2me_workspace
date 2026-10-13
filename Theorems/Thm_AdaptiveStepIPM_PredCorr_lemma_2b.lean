import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 2(b), printed p. 5. -/
theorem lemma_2b {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hxs : N2 A b c β x s) :
    (l2Norm (scaledR x s 1)) ^ 2 ≤ β ^ 2 * mu x s / (1 - β) := by sorry

end AdaptiveStepIPM.PredCorr

