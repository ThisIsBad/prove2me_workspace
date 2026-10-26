import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsPathToStrictNash

namespace YoungConventions.AdaptivePlay

/-- **`L(s)`, the length of a shortest best-reply path to a strict Nash equilibrium** (Young 1993,
*The Evolution of Conventions*, Econometrica 61:57–84, §4, p. 64, PDF p. 9): "For each
strategy-tuple `s`, let `L(s)` be the length of a shortest directed path in the best reply graph
from `s` to a strict Nash equilibrium."

`shortestPathLength u s` is the least `n` such that a directed path of `n` edges leads from `s` to a
strict pure Nash equilibrium.

**Formalization Note.** Defined as `sInf` of a set of natural numbers. In a weakly acyclic game
(the only setting in which the paper and the theorems of this mission use `L(s)`) the set is
nonempty for every `s` (a sink is a strict Nash equilibrium), so the value is the true minimum; the
convention `sInf ∅ = 0` of Lean is never reached under that hypothesis. -/
noncomputable def shortestPathLength {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : ℕ :=
  sInf {n : ℕ | IsPathToStrictNash u s n}

end YoungConventions.AdaptivePlay
