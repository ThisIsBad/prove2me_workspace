import Mathlib
import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem rflp_ordered_assignments {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (q : ℝ) (u : Fin m) (hq0 : 0 < q) (hq1 : q < 1) (hh : ∀ i, 0 < h i)
    (x : Fin m → ℝ) (y : Fin n → Fin m → Fin m → ℝ) (hopt : RFLPOptimal h c f q u x y)
    (i : Fin n) (j k : Fin m) (r r' : Fin m) (hr : r.val + 2 < m) (hr' : r'.val = r.val + 1)
    (hj : y i j r = 1) (hk : y i k r' = 1) : c i j ≤ c i k := by sorry

end SupplyChainTheory
