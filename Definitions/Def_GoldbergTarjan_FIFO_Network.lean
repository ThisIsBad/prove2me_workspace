import Mathlib

namespace GoldbergTarjan.FIFO

/-- A flow network (Goldberg–Tarjan 1988, §2, p. 923). The vertex set is the finite type `V`
(`n = Fintype.card V`). The capacity `c v w` is defined on **all** ordered vertex pairs: it is
positive exactly on the edges `(v, w) ∈ E` and `0` on every other pair ("we extend the capacity
function to all vertex pairs by defining `c(v, w) = 0` if `(v, w) ∉ E`"), so `E` is the support of
`c`. The graph has no loops (`c v v = 0`). The source `s` and the sink `t` are distinct. -/
structure Network (V : Type) [Fintype V] [DecidableEq V] where
  /-- capacity of the ordered vertex pair `(v, w)`; `0` when `(v, w)` is not an edge -/
  c : V → V → ℝ
  /-- the source -/
  s : V
  /-- the sink -/
  t : V
  c_nonneg : ∀ v w, 0 ≤ c v w
  c_self : ∀ v, c v v = 0
  s_ne_t : s ≠ t

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The flow excess `e(v) = ∑_{u ∈ V} f(u, v)`, the net flow into `v` (p. 924). Here `f` is any
real-valued function on vertex pairs. -/
def excess (f : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, f u v

/-- The residual capacity `r_f(v, w) = c(v, w) − f(v, w)` (p. 924). -/
def residual (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  N.c v w - f v w

/-- A preflow (p. 924): a real-valued function on vertex pairs satisfying the capacity
constraint (1) `f(v, w) ≤ c(v, w)` and the antisymmetry constraint (2) `f(v, w) = −f(w, v)` for
all pairs, and the nonnegativity constraint (4) `∑_u f(u, v) ≥ 0` for all `v ∈ V − {s}`. -/
def IsPreflow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, f v w ≤ N.c v w) ∧ (∀ v w, f v w = -f w v) ∧ (∀ v, v ≠ N.s → 0 ≤ excess f v)

/-- `w` is reachable from `v` in the residual graph `G_f = (V, E_f)`, whose edges are the residual
edges `(a, b)` with `r_f(a, b) > 0` (p. 924): there is a (possibly empty) directed path of residual
edges from `v` to `w`. -/
def ResidualReachable (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  Relation.ReflTransGen (fun a b => 0 < residual N f a b) v w

/-- A vertex `v` is active (p. 925) if `v ∈ V − {s, t}`, `d(v) < ∞` and `e(v) > 0`. Labels take
values in `ℕ∞` (the nonnegative integers and infinity). -/
def IsActive (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  v ≠ N.s ∧ v ≠ N.t ∧ d v < ⊤ ∧ 0 < excess f v

end GoldbergTarjan.FIFO
