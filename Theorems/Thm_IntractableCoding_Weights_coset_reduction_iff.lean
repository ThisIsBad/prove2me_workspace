import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- The COSET WEIGHTS instance `(B, 11⋯1, |T|)` built from a 3DM instance is a yes-instance
iff the 3DM instance has a matching. -/
theorem coset_reduction_iff (I : ThreeDMInstance) :
    ThreeDMYes I ↔ CosetWeightsYes (cosetOf3DM I) := by sorry

end IntractableCoding.Weights

