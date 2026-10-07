import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem lemma_2_adjacent_min_tree {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ) :
    ∃ T : Finset (Fin n), IsAdjTree φ T ∧
      ∀ E : Finset (Fin (n + 1) × Fin (n + 1)), IsSpanningTree φ E →
        adjTreeCost f g A B φ T ≤ arcSetCost f g A B φ E := by sorry

end GilmoreGomoryTSP.MinCost

