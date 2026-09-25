import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem lagrangian_equals_lp {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (hm : 0 < m) : uflpLP h c f = zLRbest h c f := by sorry

end SupplyChainTheory
