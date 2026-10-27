import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- The code with parity-check matrix `A = subspaceMatrix I` has a word of weight
`3n² + 4n` iff the set of triples admits a matching. -/
theorem subspace_reduction_iff (I : ThreeDMInstance) :
    ThreeDMYes I ↔ SubspaceWeightsYes (subspaceOf3DM I) := by sorry

end IntractableCoding.Weights

