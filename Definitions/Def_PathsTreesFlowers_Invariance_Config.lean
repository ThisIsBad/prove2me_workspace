import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink

namespace PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The output of construction 6.0 (Edmonds 1965, pp. 463–464) applied to `(G, M)` with `M` a
maximum matching: the graph `G* = shrink G P` obtained by shrinking nested blossoms for `M`, with
`M* = M/P`, and a sequence `J₁, …, Jₙ` of disjoint planted trees in `G*`. The fields record every
invariant the construction establishes:

* `M` is a maximum matching of `G`;
* every part of `P` is a blossom set for `M` (the complete expansion of a pseudovertex, or a single
  vertex);
* each `Jᵢ` is a planted tree for `M*` in `G*`, and the trees are pairwise vertex-disjoint;
* every vertex of `G*` exposed for `M*` lies in some `Jᵢ` (the forest is *dense*, 4.20): there is
  one tree for each exposed vertex;
* `Jᵢ` is Hungarian in `G* − J₁ − ⋯ − J_{i−1}` (6.1): every edge of `G*` at an outer vertex of
  `Jᵢ` ends at an inner vertex of `Jᵢ` or at a vertex of an earlier tree;
* every pseudovertex of `G*` (a part with more than one vertex) is an outer vertex of some `Jᵢ`. -/
structure Config60 (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) where
  /-- `M` is a maximum matching of `G` -/
  hM : PathsTreesFlowers.Duality.IsMaxMatching G M
  /-- the partition of the vertices of `G` into the complete expansions of the vertices of `G*` -/
  P : Finpartition (Finset.univ : Finset V)
  /-- every part is a blossom set for `M` -/
  blossom : ∀ U ∈ P.parts, PathsTreesFlowers.Duality.IsBlossomSet G M U
  /-- the number of trees -/
  n : ℕ
  /-- the trees `J₁, …, Jₙ` (indexed from `0`) in `G*` -/
  J : Fin n → AltTree (shrink G P)
  /-- each `Jᵢ` is a planted tree for `M*` in `G*` -/
  planted : ∀ i, ∃ r, IsPlantedTree (shrink G P) (shrinkMatching G P M) (J i) r
  /-- the trees are pairwise disjoint -/
  disjoint : ∀ i j, i ≠ j → Disjoint (J i).verts (J j).verts
  /-- dense: every vertex of `G*` exposed for `M*` is a vertex of some tree -/
  dense : ∀ x, PathsTreesFlowers.Duality.IsExposed (shrink G P) (shrinkMatching G P M) x → ∃ i, x ∈ (J i).verts
  /-- `Jᵢ` is Hungarian in `G* − J₁ − ⋯ − J_{i−1}` -/
  ordered_hungarian : ∀ i, ∀ u ∈ (J i).outer, ∀ (e : ShrinkE G P) (w : {U // U ∈ P.parts}),
    (shrink G P).ends e = s(u, w) → w ∈ (J i).inner ∨ ∃ h < i, w ∈ (J h).verts
  /-- every pseudovertex of `G*` is an outer vertex of some tree -/
  pseudo_outer : ∀ (U : Finset V) (hU : U ∈ P.parts), 1 < U.card → ∃ i, ⟨U, hU⟩ ∈ (J i).outer

variable {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}

/-- The *outer vertices* `O(G)` of `G` (6.2 (a), p. 464): the non-pseudo outer vertices of the
`Jᵢ` (vertices `v` whose part `{v}` is an outer vertex of some tree) together with the vertices of
the pseudovertex complete expansions (vertices whose part has more than one vertex). -/
def outerSet (C : Config60 G M) : Set V :=
  {v | ((C.P.part v).card = 1 ∧ ∃ i, partOf C.P v ∈ (C.J i).outer) ∨ 1 < (C.P.part v).card}

/-- The *inner vertices* `I(G)` of `G` (6.2 (b), p. 464): the vertices whose part is an inner
vertex of some `Jᵢ`. -/
def innerSet (C : Config60 G M) : Set V :=
  {v | ∃ i, partOf C.P v ∈ (C.J i).inner}

end PathsTreesFlowers.Invariance
