import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.MinCost

theorem theorem_5_psiStar_minimal {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : RanksA A φ)
    (T : Finset (Fin n)) (hT : IsMinCostAdjTree f g A B φ T) :
    IsTour (psiStar A B φ T) ∧
      ∀ ψ : Equiv.Perm (Fin (n + 1)), IsTour ψ →
        cost f g A B (psiStar A B φ T) ≤ cost f g A B ψ := by sorry

end GilmoreGomoryTSP.MinCost

