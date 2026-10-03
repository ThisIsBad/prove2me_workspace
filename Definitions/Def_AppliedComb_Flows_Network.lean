import Mathlib

namespace AppliedComb.Flows

/-- A network (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 259, Section 13.1)
on a finite vertex set `V`.

* `adj x y` says that the directed edge `(x, y)` is present. The underlying directed graph is
  an **oriented graph**: for each pair of vertices `x, y` at most one of `(x, y)` and `(y, x)`
  is an edge (`oriented`; taking `x = y` this also excludes loops).
* `S` is the **source** and `T` the **sink**, two distinct vertices. All edges incident with the
  source are oriented away from the source (`no_edge_into_source`), and all edges incident with
  the sink are oriented towards the sink (`no_edge_out_of_sink`).
* `cap x y` is the **capacity** `c(x, y)` of the edge `(x, y)`, a non-negative real number
  (`cap_nonneg`). Values of `cap` on pairs that are not edges are never used. -/
structure Network (V : Type*) [Fintype V] [DecidableEq V] where
  /-- `adj x y` : the directed edge `(x, y)` belongs to the network. -/
  adj : V → V → Prop
  /-- The source `S`. -/
  S : V
  /-- The sink `T`. -/
  T : V
  /-- The capacity `c(x, y)` of the edge `(x, y)`. -/
  cap : V → V → ℝ
  source_ne_sink : S ≠ T
  oriented : ∀ x y, adj x y → ¬ adj y x
  no_edge_into_source : ∀ x, ¬ adj x S
  no_edge_out_of_sink : ∀ y, ¬ adj T y
  cap_nonneg : ∀ x y, adj x y → 0 ≤ cap x y

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **flow** `ϕ` in the network `N` (Keller & Trotter, pp. 259–260): a function assigning to
each directed edge `e = (x, y)` a value with `0 ≤ ϕ(x, y) ≤ c(x, y)`, extended by the book's
convention `ϕ(x, y) = 0` when `(x, y)` is not an edge (p. 262), such that the conservation
laws hold:
1. `∑ₓ ϕ(S, x) = ∑ₓ ϕ(x, T)` (the amount leaving the source equals the amount arriving at the
   sink);
2. for every vertex `y` other than the source and the sink, `∑ₓ ϕ(x, y) = ∑ₓ ϕ(y, x)`. -/
def IsFlow (N : Network V) (ϕ : V → V → ℝ) : Prop :=
  (∀ x y, N.adj x y → 0 ≤ ϕ x y ∧ ϕ x y ≤ N.cap x y) ∧
  (∀ x y, ¬ N.adj x y → ϕ x y = 0) ∧
  (∑ x, ϕ N.S x = ∑ x, ϕ x N.T) ∧
  (∀ y, y ≠ N.S → y ≠ N.T → ∑ x, ϕ x y = ∑ x, ϕ y x)

/-- The **value** of a flow `ϕ` (p. 260): the amount `∑ₓ ϕ(S, x)` leaving the source. -/
def value (N : Network V) (ϕ : V → V → ℝ) : ℝ :=
  ∑ x, ϕ N.S x

/-- A **cut** (p. 261): a partition `V = L ∪ U` of the vertex set with `S ∈ L` and `T ∈ U`.
It is represented by the part `L`; the other part is `U = Lᶜ`. -/
def IsCut (N : Network V) (L : Finset V) : Prop :=
  N.S ∈ L ∧ N.T ∉ L

open Classical in
/-- The **capacity** `c(L, U)` of the cut `V = L ∪ U` (p. 261): the total capacity of all edges
from `L` to `U = Lᶜ`,
`c(L, U) = ∑_{x ∈ L, y ∈ U} c(x, y)`, where only directed edges `(x, y)` with `x ∈ L`, `y ∈ U`
are counted (edges from `U` to `L` are not included). -/
noncomputable def cutCapacity (N : Network V) (L : Finset V) : ℝ :=
  ∑ x ∈ L, ∑ y ∈ Lᶜ, if N.adj x y then N.cap x y else 0

end Network

end AppliedComb.Flows
