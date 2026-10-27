import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- A 3DM instance has a matching iff some `|T|` rows of its triple incidence matrix have
mod 2 sum `11⋯1`: the chosen rows are the support of a 0/1 row vector `x` of weight `|T|`. -/
theorem matching_iff_rows_sum_ones (I : ThreeDMInstance) :
    ThreeDMYes I ↔ ∃ x : Fin (tCount I) → ZMod 2,
      hammingNorm x = I.1 ∧ Matrix.vecMul x (incidence I) = fun _ => 1 := by sorry

end IntractableCoding.Weights

