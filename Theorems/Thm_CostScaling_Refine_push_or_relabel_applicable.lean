import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Lemma 5.1, p. 19. Feasibility also rules out an empty relabel minimum. -/
theorem push_or_relabel_applicable {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (s : State V)
    (hfeasible : ∃ g, CycleCanceling.MinMean.IsCirculation N g)
    (hopt : IsEpsOptimal N ε s.f s.p) (v : V) (hv : IsActive N s.f v) :
    (∃ w, PushApplicable N s v w) ∨ (∃ t, IsRelabelStep N ε s v t) := by sorry

end CostScaling.Refine

