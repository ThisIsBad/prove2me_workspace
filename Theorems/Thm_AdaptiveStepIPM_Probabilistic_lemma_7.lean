import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Lemma 7 for an arbitrary sequence of orthogonal frames. -/
theorem lemma_7 (F : ∀ n : ℕ, 2 ≤ n → Frame n) :
    Tendsto (fun n : ℕ =>
      if hn : 2 ≤ n then
        ((sphereGaussian (n - 1))
          {v | supNorm ((F n hn).H v) ≤
            Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ))}).toReal
      else 1) atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic

