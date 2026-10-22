import Mathlib

namespace BNCovPack.Routing

/-! Fractional routings of a sequence of requests (Buchbinder–Naor 2009, §5.2, p. 14, Fig. 3).

The edge set is a finite type `E`. A request `r_i` is given by the list of its admissible paths
`P(r_i)`, each path being a finite set of edges. The arrival sequence of requests is a
`List (List (Finset E))`. A fractional routing assigns to the `j`-th path of the `i`-th request a
flow value `f(r_i, P)`; it is stored as a `List (List ℝ)` of the same shape. -/

/-- `pathLoad e ps fs = ∑_{j : e ∈ ps[j]} fs[j]`: the flow through edge `e` on the paths `ps` of a
single request, when path `ps[j]` carries flow `fs[j]` (lists are traversed in parallel). -/
def pathLoad {E : Type*} [DecidableEq E] (e : E) : List (Finset E) → List ℝ → ℝ
  | P :: ps, y :: ys => (if e ∈ P then y else 0) + pathLoad e ps ys
  | _, _ => 0

/-- `edgeLoad e σ f = ∑_{r_i} ∑_{P ∈ P(r_i) | e ∈ P} f(r_i, P)`: the total flow through edge `e`
(the left-hand side of the capacity constraint of Fig. 3). -/
def edgeLoad {E : Type*} [DecidableEq E] (e : E) : List (List (Finset E)) → List (List ℝ) → ℝ
  | ps :: σ, fs :: f => pathLoad e ps fs + edgeLoad e σ f
  | _, _ => 0

/-- The value `∑_{r_i} ∑_{P ∈ P(r_i)} f(r_i, P)` of a fractional routing (the objective of
Fig. 3). -/
def routingValue (f : List (List ℝ)) : ℝ :=
  (f.map List.sum).sum

/-- `f` is a feasible fractional routing of the request sequence `σ` with capacities `u`
(Fig. 3, p. 14):
1. `f` has the shape of `σ` (one flow value per path of each request) and is non-negative;
2. every request receives total flow `∑_{P ∈ P(r_i)} f(r_i, P) ≤ 1`;
3. every edge carries total flow at most its capacity, `edgeLoad e σ f ≤ u e`. -/
def IsFeasibleRouting {E : Type*} [DecidableEq E] (u : E → ℝ) (σ : List (List (Finset E)))
    (f : List (List ℝ)) : Prop :=
  List.Forall₂ (fun ps fs => fs.length = ps.length ∧ ∀ y ∈ fs, 0 ≤ y) σ f ∧
  (∀ fs ∈ f, fs.sum ≤ 1) ∧
  ∀ e, edgeLoad e σ f ≤ u e

end BNCovPack.Routing
