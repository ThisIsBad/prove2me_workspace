import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Invariance

open EdmondsMatching65.Polyhedron (IsMatching)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A subgraph of `G` (3.0): a set of vertices and a set of edges of `G` whose end-points lie in
that vertex set. -/
structure Sub (G : EdmondsMatching65.Polyhedron.Graph V E) where
  /-- the vertices of the subgraph -/
  verts : Finset V
  /-- the edges of the subgraph -/
  edges : Finset E
  /-- every end-point of an edge of the subgraph is a vertex of the subgraph -/
  ends_mem : ∀ e ∈ edges, ∀ v ∈ G.ends e, v ∈ verts

/-- `M` is a maximum matching *of the subgraph* `H`: a matching of `G` using only edges of `H`, of
largest cardinality among all such matchings. -/
def IsMaxMatchingIn (G : EdmondsMatching65.Polyhedron.Graph V E) (H : Sub G) (M : Finset E) :
    Prop :=
  M ⊆ H.edges ∧ IsMatching G M ∧
    ∀ M' : Finset E, M' ⊆ H.edges → IsMatching G M' → M'.card ≤ M.card

/-- The subgraph `U⁺ = G − (G − U)` induced on a vertex set `U` (4.9, p. 456): the vertices `U`
and all edges of `G` with both end-points in `U`. "`G − H`" (3.2) is `induced G (univ \ H.verts)`. -/
def induced (G : EdmondsMatching65.Polyhedron.Graph V E) (U : Finset V) : Sub G where
  verts := U
  edges := Finset.univ.filter (fun e => G.ends e ∈ U.sym2)
  ends_mem := by
    intro e he v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_sym2_iff.1 he v hv

/-- Two vertices are adjacent in the subgraph `H`: some edge of `H` joins them. -/
def Sub.Adj {G : EdmondsMatching65.Polyhedron.Graph V E} (H : Sub G) (a b : V) : Prop :=
  ∃ e ∈ H.edges, G.ends e = s(a, b)

/-- A subgraph is *connected*: it has a vertex, and any two of its vertices are joined by a
sequence of edges of the subgraph. -/
def Sub.Connected {G : EdmondsMatching65.Polyhedron.Graph V E} (H : Sub G) : Prop :=
  H.verts.Nonempty ∧ ∀ x ∈ H.verts, ∀ y ∈ H.verts, Relation.ReflTransGen H.Adj x y

/-- An *alternating tree* `J` in `G` (4.0 (3), 4.1, p. 454): a tree — a connected subgraph with
one more vertex than edges — whose vertices are split into *inner* and *outer* vertices so that
each edge of `J` joins an inner vertex to an outer vertex and each inner vertex meets exactly two
edges of `J`. -/
structure AltTree (G : EdmondsMatching65.Polyhedron.Graph V E) extends Sub G where
  /-- the inner vertices -/
  inner : Finset V
  /-- the outer vertices -/
  outer : Finset V
  /-- the vertices of the tree are its inner and its outer vertices -/
  verts_eq : verts = inner ∪ outer
  /-- no vertex is both inner and outer -/
  disjoint_inner_outer : Disjoint inner outer
  /-- each edge joins an inner vertex to an outer vertex -/
  edge_inner_outer : ∀ e ∈ edges, ∃ u ∈ inner, ∃ w ∈ outer, G.ends e = s(u, w)
  /-- each inner vertex meets exactly two edges of the tree -/
  inner_degree : ∀ u ∈ inner, (edges.filter (fun e => u ∈ G.ends e)).card = 2
  /-- a tree is connected … -/
  connected : toSub.Connected
  /-- … with one more vertex than edges (4.0, definition (3)) -/
  card_verts : verts.card = edges.card + 1

/-- A *planted tree* `J = J(M)` of `G` for `M` with root `r` (4.3, pp. 454–455): an alternating
tree such that `M ∩ J` is a maximum matching of `J`, and the vertex `r` of `J` which is exposed
for `M ∩ J` is also exposed for `M`. -/
structure IsPlantedTree (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E)
    (J : AltTree G) (r : V) : Prop where
  /-- `M ∩ J` is a maximum matching of `J` -/
  max_in : IsMaxMatchingIn G J.toSub (M ∩ J.edges)
  /-- the root is a vertex of `J` -/
  root_mem : r ∈ J.verts
  /-- the root is exposed for `M ∩ J` -/
  root_exposed_in : PathsTreesFlowers.Duality.IsExposed G (M ∩ J.edges) r
  /-- the root is also exposed for `M` -/
  root_exposed : PathsTreesFlowers.Duality.IsExposed G M r

end PathsTreesFlowers.Invariance
