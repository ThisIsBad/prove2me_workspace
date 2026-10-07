import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, p. 116: in a symmetric mixed graph every node set `S` has as many directed edges
directed away from a node of `S` and toward a node not in `S` as directed edges directed toward
a node of `S` and away from a node not in `S`. -/
theorem cut_balance_of_symmetric {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (S : Finset V) :
    (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S ∧ G.head e ∉ S)).card =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S ∧ G.tail e ∉ S)).card := by sorry

end ChinesePostman.Mixed

