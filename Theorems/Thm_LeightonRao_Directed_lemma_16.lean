import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Lemma 16, p. 807. A nonnegative distance function of total weight `W` satisfying
the directed distance constraint yields a directed cut of ratio cost at most `(1152/5) W log₂ n`
(Corollary 14's bound; it dominates Lemma 15's `12 W` since `log₂ n ≥ 1`). -/
theorem lemma_16 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (hconn : IsStronglyConnectedNet N)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (hW : SatisfiesDiConstraint N d) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      diRatio N U ≤ (1152 / 5) * diTotalWeight N d * Real.logb 2 (Fintype.card V) := by sorry

end LeightonRao.Directed

