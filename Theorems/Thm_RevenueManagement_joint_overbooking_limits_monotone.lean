import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem joint_overbooking_limits_monotone {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ)
    (Cap : Fin (m + 1) → ℝ) (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) (i j : Fin n) (hij : i ≠ j) :
    jointLimit h Cap p s q y (x + Pi.single j 1) i ≤ jointLimit h Cap p s q y x i := by sorry

end RevenueManagement
