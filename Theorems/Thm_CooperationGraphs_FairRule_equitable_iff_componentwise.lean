import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, (16): a rule `Y` satisfies the equity condition (10) iff for every
graph `g` and every component `S ∈ N/g` there is a number `d(S,g)` with
`Y_i(g) − t_i(g) = d(S,g)` for all `i ∈ S`. -/
theorem equitable_iff_componentwise {n : ℕ} (hn : 0 < n) (Y : Rule n) :
    IsEquitable Y ↔ ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g,
      ∃ d : ℝ, ∀ i ∈ S, Y g i - altSum Y g i = d := by sorry

end CooperationGraphs.FairRule

