import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem bertrand_edgeworth_pure_equilibria {n : ℕ} (hn : 2 ≤ n) (a c C : ℝ) (hac : c < a)
    (hC : 0 < C) :
    ((a - c) / (n - 1) ≤ C →
      IsBEEquilibrium a c C (fun _ : Fin n => c) ∧ ∀ i, bePayoff a c C (fun _ : Fin n => c) i = 0) ∧
    (C ≤ (a - c) / (n + 1) → IsBEEquilibrium a c C (fun _ : Fin n => a - n * C)) := by sorry

end RevenueManagement
