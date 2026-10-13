import Mathlib

namespace EHRR10.LowerBound

/-- Condition i) of Eisenbrand–Hähnle–Razborov–Rothvoß (Dagstuhl 10211, 2010, p. 2): for each
`u, v ∈ V` there is a walk in `G` from `u` to `v` every vertex of which contains `u ∩ v`.
(A walk suffices: every walk contains a path on a subset of its vertices; the endpoints contain
`u ∩ v` trivially, so "every vertex" is the same as "every intermediate vertex".) -/
def CondI {n : ℕ} (V : Finset (Finset (Fin n))) (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ p : G.Walk u v, ∀ w ∈ p.support,
    (u : Finset (Fin n)) ∩ (v : Finset (Fin n)) ⊆ (w : Finset (Fin n))

/-- The base abstraction `𝓑_{d,n}`: a graph `G` on a nonempty family `V` of `d`-element subsets of
`[n]` (here `Fin n`) satisfying condition i). -/
def InB (d n : ℕ) (V : Finset (Finset (Fin n))) (G : SimpleGraph V) : Prop :=
  V.Nonempty ∧ (∀ v ∈ V, v.card = d) ∧ CondI V G

end EHRR10.LowerBound
