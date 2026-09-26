import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem monotone_best_responses_equilibrium {m n : ℕ} (u1 u2 : Fin m → Fin n → ℝ) (hm : 0 < m)
    (hn : 0 < n) (h : (NoCrossing1 u1 ∧ NoCrossing2 u2) ∨ (ReverseCrossing1 u1 ∧ ReverseCrossing2 u2)) :
    ∃ i j, IsNashEquilibrium u1 u2 i j := by sorry

end RevenueManagement
