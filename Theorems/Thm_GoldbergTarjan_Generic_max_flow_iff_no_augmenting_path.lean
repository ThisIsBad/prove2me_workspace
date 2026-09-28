import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow

namespace GoldbergTarjan.Generic

/-- Theorem 3.2 (Ford–Fulkerson; Goldberg–Tarjan 1988, p. 926). A flow `f` is maximum if and
only if there is no augmenting path, that is, `t` is not reachable from `s` in `G_f`. -/
theorem max_flow_iff_no_augmenting_path {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ResidualReachable N f N.s N.t := by sorry

end GoldbergTarjan.Generic

