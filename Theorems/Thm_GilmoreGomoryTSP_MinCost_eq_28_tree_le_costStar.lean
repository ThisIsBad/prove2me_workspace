import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

namespace GilmoreGomoryTSP.MinCost

theorem eq_28_tree_le_costStar {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (ψ : Equiv.Perm (Fin (n + 1))) (hψ : IsTour ψ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    adjTreeCost f g A B φ T ≤ costStar f g A B φ ψ := by sorry

end GilmoreGomoryTSP.MinCost

