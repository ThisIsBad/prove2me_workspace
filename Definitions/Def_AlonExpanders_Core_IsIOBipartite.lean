import Mathlib

namespace AlonExpanders.Core

/-- `G` is a bipartite graph on the sets of vertices `I` (inputs) and `O` (outputs)
(Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §1, p. 83): the vertex set is the
disjoint union `I ⊕ O` and no edge joins two inputs or two outputs. -/
def IsIOBipartite {I O : Type} (G : SimpleGraph (I ⊕ O)) : Prop :=
  (∀ i i' : I, ¬ G.Adj (Sum.inl i) (Sum.inl i')) ∧ (∀ o o' : O, ¬ G.Adj (Sum.inr o) (Sum.inr o'))

end AlonExpanders.Core
