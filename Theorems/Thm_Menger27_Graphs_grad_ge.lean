import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

theorem grad_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) :
    n ≤ G.edgeFinset.card := by sorry

end Menger27.Graphs

