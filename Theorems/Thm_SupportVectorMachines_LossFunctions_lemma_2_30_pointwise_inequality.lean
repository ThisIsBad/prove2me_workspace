import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

namespace SupportVectorMachines.LossFunctions

/-- Lemma 2.30, p. 36, Eq. (2.15): for all `η ∈ [0,1]` and all `t ∈ [-1,1]`,
`|2η - 1| · 1_{(-∞,0]}((2η - 1) · sign t) ≤ |2η - 1| · |t - sign(2η - 1)|`. -/
theorem lemma_2_30_pointwise_inequality (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (if (2 * η - 1) * sgn t ≤ 0 then |2 * η - 1| else 0) ≤
      |2 * η - 1| * |t - sgn (2 * η - 1)| := by sorry

end SupportVectorMachines.LossFunctions
