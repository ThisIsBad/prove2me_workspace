import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem exists_separator_through {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card)
    (s : V) (hsP : s ∉ P) (hsQ : s ∉ Q) (t : V) (hst : K.Adj s t) :
    ∃ S : Finset V, s ∈ S ∧ S.card = n ∧ Separates K P Q S := by sorry

end Menger27.Graphs

