import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_Backtracking

namespace Timetabling85.TwoPeriod

theorem autarky {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (A : Finset (Fin n × Bool)) (hA : G.IsIndepSet (A : Set (Fin n × Bool)))
    (hclosed : closure G A = A) :
    (∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) ↔
      ∃ T : Finset (Fin n × Bool), A ⊆ T ∧ G.IsNIndepSet n T := by sorry

end Timetabling85.TwoPeriod

