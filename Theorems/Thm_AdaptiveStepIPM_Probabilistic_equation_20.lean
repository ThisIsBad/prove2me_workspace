import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Equation (20), the high dimensional Gaussian norm lower bound. -/
theorem equation_20 (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin (n - 1))))
        {w | (1 - ε) * Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ ‖w‖}).toReal)
      atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic

