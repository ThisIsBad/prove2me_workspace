import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem B_univ_eq_sum_balancing {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) (T : Finset (Finset N)) (x : N → ℝ)
    (δ : Finset N → ℝ)
    (hT : IsBalancedFamily T)
    (hx : ∀ S ∈ T, x ∈ marketGame A S)
    (hδ : IsBalancingWeights T δ) :
    acceptableMatrix A Finset.univ x =
      ∑ S ∈ T, δ S • acceptableMatrix A S x := by sorry

end ShapleyScarf.Balanced

