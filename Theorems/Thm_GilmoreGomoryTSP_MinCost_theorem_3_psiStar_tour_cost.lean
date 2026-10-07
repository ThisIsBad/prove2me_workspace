import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_3_psiStar_tour_cost {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    IsTour (psiStar A B φ T) ∧
      cost f g A B (psiStar A B φ T) = cost f g A B φ + adjTreeCost f g A B φ T := by sorry

end GilmoreGomoryTSP.MinCost

