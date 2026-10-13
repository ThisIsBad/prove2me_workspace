import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open ProjSchedTW.Complexity

/-- Proof of LEMMA 1, p. 333: for a partition instance `Y = [y₁, …, yₙ]` with `n ≥ 1` and every
`yᵢ > 1`, the list `X` with `x₁ = 1`, `x₂ᵢ = x₂ᵢ₋₁ + yᵢ`, `x₂ᵢ₊₁ = x₂ᵢ + 1` is an even-odd
partition instance, and `Y` has a partition into two parts of equal sum iff `X` has an even-odd
partition into two parts of equal sum. -/
theorem lemma_1_construction (y : List ℕ) (hy : y ≠ []) (hy1 : ∀ v ∈ y, 1 < v) :
    EOInstance (eoOfPartition y) ∧ (PartitionYes y ↔ EOYes (eoOfPartition y)) := by sorry

end GTWSched.NPC

