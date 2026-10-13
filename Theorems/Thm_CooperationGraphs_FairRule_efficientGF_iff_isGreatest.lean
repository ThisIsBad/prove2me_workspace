import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, (17): if `Y` satisfies (16) with numbers `d(S,g)`, then `Y` satisfies
the efficiency condition (14) iff for every embedded subgraph `(S, g)`, `d(S,g)` is the maximum of
`{x | (x + t_i(g))_{i ∈ S} ∈ w(S,g)}`. -/
theorem efficientGF_iff_isGreatest {n : ℕ} (hn : 0 < n) (G : GraphFunctionGame n) (Y : Rule n)
    (d : SimpleGraph (Fin n) → Finset (Fin n) → ℝ)
    (hd : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, ∀ i ∈ S, Y g i - altSum Y g i = d g S) :
    IsEfficientGF G Y ↔
      ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g,
        IsGreatest {x : ℝ | (fun i : ↥S => x + altSum Y g i) ∈ G.w g S} (d g S) := by sorry

end CooperationGraphs.FairRule

