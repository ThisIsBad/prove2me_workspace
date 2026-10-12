import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_Backtracking

namespace Timetabling85.TwoPeriod

theorem limited_backtracking_correct {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true)) :
    Acc (fun t s => Step G s t) (State.run ∅) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∃ j, ¬ Fixed A j) →
      ∃ t, Step G (State.run A) t) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∀ j, Fixed A j) →
      G.IsNIndepSet n A) ∧
    (Reachable G State.fail → ¬ ∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) := by sorry

end Timetabling85.TwoPeriod

