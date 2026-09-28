import Mathlib
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory

namespace RobustMeanCov.OnePoint

theorem quadratic_lower_bound (u : ℝ → ℝ) (m s : ℝ) (ν : Measure ℝ)
    (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m (s ^ 2)) (hint : Integrable u ν) (A B C : ℝ)
    (hq : ∀ y : ℝ, A * y ^ 2 + B * y + C ≤ u y) :
    A * (m ^ 2 + s ^ 2) + B * m + C ≤ ∫ y, u y ∂ν := by sorry

end RobustMeanCov.OnePoint
