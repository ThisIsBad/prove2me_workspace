import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 1(a), equation (9), printed p. 5. -/
theorem lemma_1a {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s dx ds : Fin n → ℝ) (dy : Fin m → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hxs : F0 A b c x s)
    (hd : SearchDirection A x s γ dx dy ds) :
    l2Norm (Pq x s dx ds) ≤
      (Real.sqrt 2 / 4) * (l2Norm (scaledR x s γ)) ^ 2 := by sorry

end AdaptiveStepIPM.PredCorr

