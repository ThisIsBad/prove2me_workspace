import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem cournot_linear_equilibrium {n : ℕ} (a c : ℝ) (hac : c < a) :
    (∀ (i : Fin n) (xi : ℝ), 0 ≤ xi →
      cournotPayoff a c (Function.update (fun _ => (a - c) / (n + 1)) i xi) i ≤
        cournotPayoff a c (fun _ => (a - c) / (n + 1)) i) ∧
    a - n * ((a - c) / (n + 1)) = c + (a - c) / (n + 1) := by sorry

end RevenueManagement
