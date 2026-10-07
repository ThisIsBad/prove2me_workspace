import Mathlib

namespace Menger27.Graphs

/-- `Separates G P Q S` (Menger 1927, p. 99): the vertex set `S` separates `P` and `Q` in `G`,
i.e. every walk of `G` from a vertex of `P` to a vertex of `Q` passes through a vertex of `S`.
`S` may contain vertices of `P` and of `Q`. -/
def Separates {V : Type*} (G : SimpleGraph V) (P Q S : Finset V) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, ∀ w : G.Walk x y, ∃ v ∈ w.support, v ∈ S

/-- `NPointConnected G P Q n` (Menger 1927, p. 100, "n-punktig zusammenhängend"): no set of fewer
than `n` vertices separates `P` and `Q` in `G`. -/
def NPointConnected {V : Type*} (G : SimpleGraph V) (P Q : Finset V) (n : ℕ) : Prop :=
  ∀ S : Finset V, Separates G P Q S → n ≤ S.card

/-- `HasDisjointPaths G P Q n` (Menger 1927, p. 100, Satz β): `G` contains `n` pairwise
vertex-disjoint paths (endpoints included), each starting at a vertex of `P` and ending at a
vertex of `Q`. -/
def HasDisjointPaths {V : Type*} (G : SimpleGraph V) (P Q : Finset V) (n : ℕ) : Prop :=
  ∃ (a b : Fin n → V) (w : ∀ i, G.Walk (a i) (b i)),
    (∀ i, a i ∈ P ∧ b i ∈ Q ∧ (w i).IsPath) ∧
    ∀ i j, i ≠ j → List.Disjoint (w i).support (w j).support

end Menger27.Graphs
