import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values
import Definitions.Def_TheoryOfGames_PerfectInfo_backwardValue

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- 15.6.1 with (15:12): every zero-sum two-person game with perfect information (chance moves
allowed) is strictly determined, `v₁ = v₂`, and its value is given by the formula (15:12),
`v₁ = v₂ = v = M^{k₁}_{σ₁} M^{k₂(σ₁)}_{σ₂} ⋯ M^{k_ν(σ₁,…,σ_{ν-1})}_{σ_ν} 𝔉₁(π(σ₁, …, σ_ν))`. -/
theorem strictly_determined_value (t : GameTree) :
    v1 t = backwardValue t ∧ v2 t = backwardValue t := by sorry

end TheoryOfGames.PerfectInfo

