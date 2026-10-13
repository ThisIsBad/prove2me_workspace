import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- The Gaussian maximum limit used in the proof of Lemma 7. -/
theorem gaussian_maximum :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin n)))
        {w | supNorm w ≤ Real.sqrt (2 * Real.log (2 * (n : ℝ)))}).toReal)
      atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic

