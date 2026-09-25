import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_weak_duality {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) (lam : Fin n → ℝ) : zLR h c f lam ≤ uflpOpt h c f := by sorry

end SupplyChainTheory
