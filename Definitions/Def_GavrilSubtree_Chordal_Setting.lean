import Mathlib

namespace GavrilSubtree.Chordal

universe u

/-- §1, p. 48: a graph is chordal if every simple circuit with more than three vertices has an
edge connecting two non-consecutive vertices. A cycle walk of length `L` has `L` distinct
vertices and its edges are exactly the consecutive pairs, so a chord is an edge of `G` between
two vertices of the cycle that is not an edge of the cycle. -/
def IsChordal {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (c : G.Walk u u), c.IsCycle → 4 ≤ c.length →
    ∃ x ∈ c.support, ∃ y ∈ c.support, G.Adj x y ∧ s(x, y) ∉ c.edges

/-- §1, pp. 47–49: `F` represents `G` by subtrees of the tree `T`. Every `F v` is a subtree
(a nonempty vertex set inducing a connected subgraph of `T`), and two distinct vertices of `G`
are adjacent if and only if their subtrees intersect. -/
def IsSubtreeRep {V : Type u} {β : Type u} (G : SimpleGraph V) (T : SimpleGraph β)
    (F : V → Set β) : Prop :=
  T.IsTree ∧ (∀ v, (T.induce (F v)).Connected) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (F u ∩ F v).Nonempty)

/-- §1, p. 48: a subtree graph is the intersection graph of a family of subtrees of a tree. -/
def IsSubtreeGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (β : Type u) (T : SimpleGraph β) (F : V → Set β), IsSubtreeRep G T F

/-- §3, p. 54: a proper subtree graph is the intersection graph of a family of subtrees of a
tree so that no one of the subtrees is contained in another. -/
def IsProperSubtreeGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (β : Type u) (T : SimpleGraph β) (F : V → Set β),
    IsSubtreeRep G T F ∧ ∀ u v, u ≠ v → ¬ F u ⊆ F v

/-- §1, p. 47 and §2, p. 50: `μ(G)`, the cliques of `G`, i.e. the maximal completely connected
sets of vertices. -/
def Cliques {V : Type u} (G : SimpleGraph V) : Type u :=
  {s : Set V // Maximal G.IsClique s}

/-- §2, p. 50: `μ_v(G)`, the set of cliques of `G` containing the vertex `v`. -/
def cliquesAt {V : Type u} (G : SimpleGraph V) (v : V) : Set (Cliques G) :=
  {A | v ∈ A.1}

/-- Theorem 2, p. 51: there is a tree `T` whose set of vertices is `μ(G)` such that, for every
vertex `v`, the subgraph `T(μ_v(G))` is connected. -/
def HasCliqueTree {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ T : SimpleGraph (Cliques G), T.IsTree ∧ ∀ v, (T.induce (cliquesAt G v)).Connected

/-- §1, p. 48: `v` is simplicial if `Γv`, the set of its neighbours, is completely connected. -/
def IsSimplicial {V : Type u} (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

end GavrilSubtree.Chordal
