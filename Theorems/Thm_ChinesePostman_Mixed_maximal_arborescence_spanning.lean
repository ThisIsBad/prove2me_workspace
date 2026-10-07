import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, pp. 115–116: if the directed edges of a mixed graph form a symmetric, connected spanning
subgraph, then every maximal arborescence of directed edges is spanning. -/
theorem maximal_arborescence_spanning {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (hconn : G.DirectedConnected)
    (W : Finset V) (r : V) (a : V → Option E) (harb : G.IsArborescence W r a)
    (hmax : G.IsMaximalNodeSet W) :
    W = Finset.univ := by sorry

end ChinesePostman.Mixed

