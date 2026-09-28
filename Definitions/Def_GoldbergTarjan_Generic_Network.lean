import Mathlib

namespace GoldbergTarjan.Generic

/-- A flow network (Goldberg–Tarjan 1988, §2, p. 923). The vertex set is the type `V`
(finite in every use, `n = Fintype.card V`). The capacity function `c` is defined on all
vertex pairs: it is positive exactly on the edges and `0` on non-edges (the paper's
"We extend the capacity function to all vertex pairs by defining `c(v, w) = 0` if
`(v, w) ∉ E`"), so `c ≥ 0` everywhere. The graph has no loops (`c v v = 0`).
`s` is the source and `t` the sink, and they are distinct. -/
structure Network (V : Type) where
  /-- capacity `c(v, w)` of the vertex pair `(v, w)` -/
  c : V → V → ℝ
  /-- the source -/
  s : V
  /-- the sink -/
  t : V
  cap_nonneg : ∀ v w, 0 ≤ c v w
  cap_self : ∀ v, c v v = 0
  source_ne_sink : s ≠ t

variable {V : Type} [Fintype V]

/-- The edge set `E = {(v, w) | c(v, w) > 0}` of the network. -/
noncomputable def Network.edges (N : Network V) : Finset (V × V) :=
  Finset.univ.filter (fun p => 0 < N.c p.1 p.2)

/-- `m = |E|`, the number of (directed) edges. -/
noncomputable def Network.numEdges (N : Network V) : ℕ :=
  N.edges.card

end GoldbergTarjan.Generic
