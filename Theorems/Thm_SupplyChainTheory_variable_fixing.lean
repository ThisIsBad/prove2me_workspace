import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem variable_fixing {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) (lam : Fin n → ℝ) (UB : ℝ) (hUB : uflpOpt h c f ≤ UB) (j : Fin m) :
    (0 ≤ benefit h c lam j + f j → UB < zLR h c f lam + (benefit h c lam j + f j) →
        ∀ x y, UFLPFeasible x y → uflpCost h c f x y = uflpOpt h c f → x j = 0)
      ∧ (benefit h c lam j + f j < 0 → UB < zLR h c f lam - (benefit h c lam j + f j) →
        ∀ x y, UFLPFeasible x y → uflpCost h c f x y = uflpOpt h c f → x j = 1) := by sorry

end SupplyChainTheory
