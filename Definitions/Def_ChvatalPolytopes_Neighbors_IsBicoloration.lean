import Mathlib

namespace ChvatalPolytopes.Neighbors

/-- A **bicoloration** `V = B ∪ R` of a graph `T` on `V` (Chvátal 1975, p. 149, Lemma 6.1):
a partition of the vertex set into two disjoint parts `B` and `R` such that every edge of `T`
joins a vertex of `B` to a vertex of `R`. -/
def IsBicoloration {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    (B R : Finset V) : Prop :=
  Disjoint B R ∧ B ∪ R = Finset.univ ∧
    ∀ u v, T.Adj u v → (u ∈ B ∧ v ∈ R) ∨ (u ∈ R ∧ v ∈ B)

end ChvatalPolytopes.Neighbors
