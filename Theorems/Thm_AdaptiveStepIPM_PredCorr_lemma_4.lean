import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

namespace AdaptiveStepIPM.PredCorr

/-- Lemma 4, printed p. 8: the lower bound and its admissibility. -/
theorem lemma_4 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s dx ds : Fin n → ℝ) (dy : Fin m → ℝ) (θbar : ℝ)
    (hxs : N2 A b c (1 / 4) x s)
    (hd : SearchDirection A x s 0 dx dy ds)
    (hmax : IsGreatest {θ : ℝ | PredictorAdmissible A b c x s dx ds θ} θbar) :
    PredictorAdmissible A b c x s dx ds (theta1 x s dx ds) ∧
      theta1 x s dx ds ≤ θbar := by sorry

end AdaptiveStepIPM.PredCorr

