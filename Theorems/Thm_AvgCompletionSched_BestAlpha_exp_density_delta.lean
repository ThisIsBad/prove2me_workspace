import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem exp_density_delta :
    (∀ α : ℝ, 0 ≤ Real.exp α / (Real.exp 1 - 1)) ∧
      ∫ α in (0 : ℝ)..1, Real.exp α / (Real.exp 1 - 1) = 1 ∧
      ∀ β ∈ Set.Ioc (0 : ℝ) 1,
        ∫ α in (0 : ℝ)..β, (1 + α - β) / β * (Real.exp α / (Real.exp 1 - 1))
          = 1 / (Real.exp 1 - 1) := by sorry
end AvgCompletionSched.BestAlpha
