import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- §2, p. 939, property 2 of the duality mapping: if `E` is smooth, then `J` is single
valued, i.e. `J x` consists of exactly one functional for every `x`. -/
theorem duality_single_valued (hS : IsSmooth E) (x : E) :
    ∃! v : StrongDual ℝ E, v ∈ dualityMap x := by sorry

end ProximalBanach.Hybrid
