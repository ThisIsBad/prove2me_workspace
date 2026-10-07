import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem doublyStochastic_balancingCombination {N : Type*} [Fintype N] [DecidableEq N]
    [Nonempty N] (T : Finset (Finset N)) (δ : Finset N → ℝ)
    (P : Finset N → Matrix N N ℝ)
    (hT : IsBalancedFamily T) (hδ : IsBalancingWeights T δ)
    (hP : ∀ S ∈ T, IsSPermutation S (P S)) :
    (∑ S ∈ T, δ S • P S) ∈ doublyStochastic ℝ N := by sorry

end ShapleyScarf.Balanced

