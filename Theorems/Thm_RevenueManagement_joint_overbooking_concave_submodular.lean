import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem joint_overbooking_concave_submodular {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ)
    (Cap : Fin (m + 1) → ℝ) (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) (i j : Fin n) :
    expNetRevenue h Cap p s q y (x + Pi.single i 1 + Pi.single j 1) -
        expNetRevenue h Cap p s q y (x + Pi.single i 1) ≤
      expNetRevenue h Cap p s q y (x + Pi.single j 1) - expNetRevenue h Cap p s q y x := by sorry

end RevenueManagement
