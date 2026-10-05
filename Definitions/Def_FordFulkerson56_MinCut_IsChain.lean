import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network

namespace FordFulkerson56.MinCut

variable {V E : Type*} [DecidableEq E]

/-- `IsChainWalk N u w p vs`: the list of arcs `p` together with the list of vertices `vs` is an
arrangement of a chain from `u` to `w` (Ford–Fulkerson, p. 399): `vs` has one more entry than `p`,
starts at `u` and ends at `w`; the arcs are distinct and the vertices are distinct; and the `i`-th arc
joins the `i`-th and `(i+1)`-th vertices, traversed in either direction (arcs are undirected). With
`p = []` and `vs = [u]` this is the null chain joining `u` and `u`. -/
def IsChainWalk (N : Network V E) (u w : V) (p : List E) (vs : List V) : Prop :=
  vs.length = p.length + 1 ∧ vs.head? = some u ∧ vs.getLast? = some w ∧
  vs.Nodup ∧ p.Nodup ∧
  ∀ (i : ℕ) (h : i < p.length),
    (vs[i]? = some (N.tail p[i]) ∧ vs[i + 1]? = some (N.head p[i])) ∨
    (vs[i]? = some (N.head p[i]) ∧ vs[i + 1]? = some (N.tail p[i]))

/-- A chain joining `u` and `w` (Ford–Fulkerson, p. 399): a set `C` of arcs which can be arranged as a
chain walk from `u` to `w`. -/
def IsChain (N : Network V E) (u w : V) (C : Finset E) : Prop :=
  ∃ (p : List E) (vs : List V), IsChainWalk N u w p vs ∧ p.toFinset = C

end FordFulkerson56.MinCut
