import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113: a map `p` giving each node `n ≠ r` one outgoing edge
`n → p n`, such that every nonempty node set `S` with `r ∉ S` has an edge leaving `S`, forms an
arborescence with root `r`: iterating `n ↦ p n` (with `r` fixed) leads every node to `r`. -/
theorem reaches_root_of_cut_property {V : Type} [Fintype V] [DecidableEq V] (p : V → V) (r : V)
    (h : ∀ S : Finset V, S.Nonempty → r ∉ S → ∃ n ∈ S, p n ∉ S) :
    ∀ n, ∃ j : ℕ, (fun u => if u = r then r else p u)^[j] n = r := by sorry

end ChinesePostman.NextNode

