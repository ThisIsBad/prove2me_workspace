import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem exists_vertex_not_mem {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card) :
    ∃ s : V, s ∉ P ∧ s ∉ Q ∧ ∃ t : V, K.Adj s t := by sorry

end Menger27.Graphs

