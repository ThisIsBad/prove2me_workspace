import Mathlib

namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ}

/-- Stage 1 of the proof of Theorem 7.1 (p. 662): a rooted spanning tree `T = (V, E_T)` of a graph
`G` on the vertices `v_1, …, v_N`, with the vertices numbered so that every parent precedes its
children. Vertex `v_{i+1}` is the element `i : Fin N`; the root `s` is `v_1` (index `0`).
`par j = some i` says that `v_{i+1}` is the parent of `v_{j+1}` in `T`; the root has no parent.
A breadth-first search tree numbered from the top down and from left to right is one such
layout. -/
structure TreeLayout (G : SimpleGraph (Fin N)) where
  /-- The parent of each vertex in `T`; `none` exactly at the root. -/
  par : Fin N → Option (Fin N)
  par_eq_none_iff : ∀ j, par j = none ↔ j.val = 0
  /-- Parents are numbered before their children. -/
  par_lt : ∀ j i, par j = some i → i < j
  /-- Tree edges are edges of `G` (`E_T ⊆ E`). -/
  par_adj : ∀ j i, par j = some i → G.Adj i j

variable {G : SimpleGraph (Fin N)}

/-- The edges of `E \ E_T` (p. 662), each written once as `{v_i, v_j}` with `i < j`: an edge of
`G` whose larger endpoint does not have the smaller one as its parent. -/
def NonTreeEdge (L : TreeLayout G) : Type :=
  {q : Fin N × Fin N // q.1 < q.2 ∧ G.Adj q.1 q.2 ∧ L.par q.2 ≠ some q.1}

noncomputable instance NonTreeEdge.instFintype (L : TreeLayout G) : Fintype (NonTreeEdge L) := by
  classical
  exact Subtype.fintype _

instance NonTreeEdge.instDecidableEq (L : TreeLayout G) : DecidableEq (NonTreeEdge L) :=
  inferInstanceAs (DecidableEq {q : Fin N × Fin N // q.1 < q.2 ∧ G.Adj q.1 q.2 ∧ L.par q.2 ≠ some q.1})

/-- The vertices of the graph `G′ = (V′, E′)` of Stage 1 (p. 662): the vertices `v_i` of `T`, two
new vertices `u^i_1, u^i_2` for each vertex `v_i`, and two new vertices `e^{ij}_1, e^{ij}_2` for
each edge `{v_i, v_j} ∈ E \ E_T` with `i < j`. -/
inductive GPVertex (L : TreeLayout G) : Type
  | v (i : Fin N)
  | u1 (i : Fin N)
  | u2 (i : Fin N)
  | e1 (q : NonTreeEdge L)
  | e2 (q : NonTreeEdge L)
  deriving DecidableEq

/-- The edge list of `G′` (p. 662), one orientation per edge: the tree edges `{v_i, v_j} ∈ E_T`,
the edges `{u^i_2, u^i_1}` and `{u^i_1, v_i}`, and for each `{v_i, v_j} ∈ E \ E_T` with `i < j`
the edges `{v_i, e^{ij}_1}`, `{e^{ij}_1, e^{ij}_2}` and `{e^{ij}_2, u^j_2}`. -/
def gpRel (L : TreeLayout G) : GPVertex L → GPVertex L → Prop
  | .v i, .v j => L.par j = some i
  | .u2 i, .u1 j => i = j
  | .u1 i, .v j => i = j
  | .v i, .e1 q => q.1.1 = i
  | .e1 q, .e2 q' => q = q'
  | .e2 q, .u2 j => q.1.2 = j
  | _, _ => False

/-- The graph `G′` of Stage 1 (p. 662), obtained from the tree `T` (not from `G`: the edges of
`E \ E_T` are not edges of `G′`) by attaching the gadgets listed in `gpRel`. -/
def GPrime (L : TreeLayout G) : SimpleGraph (GPVertex L) :=
  SimpleGraph.fromRel (gpRel L)

end SingleMachinePrec.IntervalReduction
