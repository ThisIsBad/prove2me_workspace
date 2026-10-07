import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem lemma_5_ordered_execution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) :
    cost f g A B (applyAdj φ (execOrder A B φ T)) =
      cost f g A B φ + adjTreeCost f g A B φ T := by sorry

end GilmoreGomoryTSP.MinCost

