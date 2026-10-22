import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, §2.2 p. 796, directed analogue used in §2.4: every nonnegative distance function
satisfying the directed distance constraint has total weight at least the max-flow, and some such
distance function has total weight exactly the max-flow. -/
theorem lp_duality {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N) :
    (∀ d : V → V → ℝ, (∀ u v, 0 ≤ d u v) → SatisfiesDiConstraint N d →
        diMaxFlow N diDemand ≤ diTotalWeight N d) ∧
    (∃ d : V → V → ℝ, (∀ u v, 0 ≤ d u v) ∧ SatisfiesDiConstraint N d ∧
        diTotalWeight N d = diMaxFlow N diDemand) := by sorry

end LeightonRao.Directed

