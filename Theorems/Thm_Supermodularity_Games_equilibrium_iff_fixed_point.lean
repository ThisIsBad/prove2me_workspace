import Mathlib
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse

namespace Supermodularity.Games

theorem equilibrium_iff_fixed_point {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ) :
    IsEquilibrium S f x' ↔ x' ∈ BestJointResponse S f x' := by sorry

end Supermodularity.Games
