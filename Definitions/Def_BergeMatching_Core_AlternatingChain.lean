import Mathlib

namespace BergeMatching.Core

/-- Berge (1957), p. 842. Given a matching `V₀` of `G`, encoded as a subgraph `M` with
`M.IsMatching`, the edges of `M` are *strong* and all other edges are *weak*. A vertex `x` is
*neutral* if it is not adjacent to a strong edge, i.e. no edge of `M` contains `x`. -/
def IsNeutral {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (x : V) : Prop :=
  ∀ e ∈ M.edgeSet, x ∉ e

/-- A *maximum* matching (Problem 3, p. 842): a matching whose number of edges is at least that
of every matching of `G`. This is cardinality-maximum, not inclusion-maximal. -/
def IsMaximumMatching {V : Type} [Finite V] {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

/-- Alternation relative to an arbitrary set `S` of strong edges (p. 842): the chain `p` does
not use the same edge twice (`p.IsTrail`), and of any two consecutive edges of `p` one is in `S`
(strong) and the other is not (weak). Stated for any graph `H`, so that it serves both `G` and
the auxiliary graph `Ḡ`. -/
def IsAlternatingWrt {W : Type} {H : SimpleGraph W} (S : Set (Sym2 W)) {u v : W}
    (p : H.Walk u v) : Prop :=
  p.IsTrail ∧ p.edges.IsChain (fun e e' => (e ∈ S ↔ e' ∉ S))

/-- An *alternating chain* of `G` with respect to the matching `M` (p. 842): a walk of `G`
that uses no edge twice and whose consecutive edges alternate between edges of `M` and edges
not in `M`. Vertices may repeat. -/
def IsAlternatingChain {V : Type} {G : SimpleGraph V} (M : G.Subgraph) {u v : V}
    (p : G.Walk u v) : Prop :=
  IsAlternatingWrt M.edgeSet p

/-- A *maximum internally stable set* (Problem 1, p. 842): an independent set of `G` with at
least as many elements as every independent set of `G`. -/
def IsMaximumIndepSet {V : Type} [Finite V] (G : SimpleGraph V) (A : Set V) : Prop :=
  G.IsIndepSet A ∧ ∀ B : Set V, G.IsIndepSet B → B.ncard ≤ A.ncard

/-- A *minimum cover* (Problem 2, p. 842): a vertex cover of `G` (every edge has an endpoint in
it) with at most as many elements as every vertex cover of `G`. -/
def IsMinimumVertexCover {V : Type} [Finite V] (G : SimpleGraph V) (C : Set V) : Prop :=
  G.IsVertexCover C ∧ ∀ D : Set V, G.IsVertexCover D → C.ncard ≤ D.ncard

end BergeMatching.Core
