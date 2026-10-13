import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 4, p. 11, display before (15): for any `Y`, any graph `g` and any link
`a,b ∈ g`, the alternating sum over the subgraphs `h ⊆ g` containing `a,b` of `Y_a(h) − Y_a(h \ a,b)`
equals the alternating sum over all `h ⊆ g` of `Y_a(h)`, which equals `Y_a(g) − t_a(g)`. -/
theorem alt_sum_identity {n : ℕ} (hn : 0 < n) (Y : Rule n) (g : SimpleGraph (Fin n)) (a b : Fin n)
    (hab : g.Adj a b) :
    (∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h ≤ g ∧ h.Adj a b),
        (-1 : ℝ) ^ (numLinks g + numLinks h) * (Y h a - Y (removeLink h a b) a)) =
      ∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h ≤ g),
        (-1 : ℝ) ^ (numLinks g + numLinks h) * Y h a ∧
    (∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h ≤ g),
        (-1 : ℝ) ^ (numLinks g + numLinks h) * Y h a) =
      Y g a - altSum Y g a := by sorry

end CooperationGraphs.FairRule

