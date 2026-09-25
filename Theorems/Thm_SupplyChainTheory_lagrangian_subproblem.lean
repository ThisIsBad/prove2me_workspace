import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_subproblem {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) :
    LagrFeasible (lagrX h c f lam) (lagrY h c f lam)
      ∧ lagrObjective h c f lam (lagrX h c f lam) (lagrY h c f lam)
          = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i
      ∧ zLR h c f lam = ∑ j, min 0 (benefit h c lam j + f j) + ∑ i, lam i := by sorry

end SupplyChainTheory
