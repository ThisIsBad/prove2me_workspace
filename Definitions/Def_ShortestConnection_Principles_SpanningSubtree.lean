import Mathlib

namespace ShortestConnection.Principles

/-- The graph on all of `V` formed by a set `F` of links: two terminals are adjacent exactly when
the link joining them belongs to `F` (Prim 1957, §II: the links made so far; §IV: a spanning
subgraph of the labelled graph). -/
def linkGraph {V : Type*} (F : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 V))

/-- `F` is a spanning subtree of the labelled graph `G` (Prim 1957, pp. 1395–1396: "connection
network ↔ spanning subgraph (without closed loops) ↔ (spanning subtree)"): every link of `F` is an
edge of `G`, and the links of `F` form a tree on the whole vertex set `V`. -/
def IsSpanningSubtree {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (F : Set (Sym2 V)) ⊆ G.edgeSet ∧ (linkGraph F).IsTree

/-- The length of a set of links: the sum of the edge "lengths" `w e` over its links
(Prim 1957, p. 1389: "total length (sum of the link lengths)"). Lengths are arbitrary reals. -/
def length {V : Type*} (w : Sym2 V → ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ F, w e

/-- `F` is a shortest spanning subtree (SSS) of `G` for the edge lengths `w`
(Prim 1957, p. 1396, "shortest connection network ↔ shortest spanning subtree, SCN ↔ SSS"):
`F` is a spanning subtree of `G` whose length is at most that of every spanning subtree of `G`.
The minimum is over spanning subtrees only, never over connected spanning subgraphs. -/
def IsSSS {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V)) : Prop :=
  IsSpanningSubtree G F ∧ ∀ F' : Finset (Sym2 V), IsSpanningSubtree G F' → length w F ≤ length w F'

/-- The length `L` of a shortest spanning subtree of `G` (Prim 1957, p. 1394: "the length, L, of a
shortest connection network is simply the smallest length in this finite set of connection
network lengths"): the infimum of the lengths of all spanning subtrees of `G`. For a connected
finite `G` this set is finite and nonempty, so the infimum is attained; for a disconnected `G` the
set is empty and the value is the junk value `0`. -/
noncomputable def minLength {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  sInf (length w '' {F : Finset (Sym2 V) | IsSpanningSubtree G F})

end ShortestConnection.Principles
