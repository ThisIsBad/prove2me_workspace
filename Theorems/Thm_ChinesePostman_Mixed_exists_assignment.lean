import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, p. 118, the outcome of the assignment algorithm: a connected, even, symmetric mixed graph
`G` admits an assignment of directions to some of its undirected edges, giving a mixed graph `G'`
with the same edges and ends in which every directed edge of `G` keeps its direction, such that
`G'` is symmetric, its directed edges form a connected spanning subgraph, and its undirected edges
have even degree at every node. -/
theorem exists_assignment {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) :
    ∃ G' : MixedGraph V E,
      (∀ e, s(G'.tail e, G'.head e) = s(G.tail e, G.head e)) ∧
      (∀ e, G.directed e = true →
        G'.directed e = true ∧ G'.tail e = G.tail e ∧ G'.head e = G.head e) ∧
      G'.IsSymmetric ∧ G'.DirectedConnected ∧ (∀ n, Even (G'.undirDeg n)) := by sorry

end ChinesePostman.Mixed

