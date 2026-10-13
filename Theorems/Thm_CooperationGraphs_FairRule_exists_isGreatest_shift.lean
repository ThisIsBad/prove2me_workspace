import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, sentence after (17): for a game `w` in graph function form, an
embedded subgraph `(S, g)` and any `r ∈ ℝ^S`, the maximum of `{x | (x + r_i)_{i ∈ S} ∈ w(S,g)}`
exists. -/
theorem exists_isGreatest_shift {n : ℕ} (hn : 0 < n) (G : GraphFunctionGame n) (g : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : S ∈ quot univ g) (r : ↥S → ℝ) :
    ∃ x : ℝ, IsGreatest {x : ℝ | (fun i : ↥S => x + r i) ∈ G.w g S} x := by sorry

end CooperationGraphs.FairRule

