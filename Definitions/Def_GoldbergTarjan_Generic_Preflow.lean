import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Network

namespace GoldbergTarjan.Generic

variable {V : Type} [Fintype V]

/-- Flow excess `e(v) = ∑_{u ∈ V} f(u, v)`, the net flow into `v` (p. 924). -/
def excess (f : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, f u v

/-- A preflow (p. 924): a real-valued function on vertex pairs satisfying the capacity
constraint (1), the antisymmetry constraint (2) and the nonnegativity constraint (4):
`∑_u f(u, v) ≥ 0` for every `v ≠ s`. -/
def IsPreflow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, f v w ≤ N.c v w) ∧ (∀ v w, f v w = -f w v) ∧
    (∀ v, v ≠ N.s → 0 ≤ excess f v)

/-- A flow (p. 923): a real-valued function on vertex pairs satisfying the capacity
constraint (1), the antisymmetry constraint (2) and flow conservation (3):
`∑_u f(u, v) = 0` for every `v ∉ {s, t}`. -/
def IsFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, f v w ≤ N.c v w) ∧ (∀ v w, f v w = -f w v) ∧
    (∀ v, v ≠ N.s → v ≠ N.t → excess f v = 0)

/-- The value `|f| = ∑_{v ∈ V} f(v, t)` of a flow, the net flow into the sink (p. 924). -/
def value (N : Network V) (f : V → V → ℝ) : ℝ :=
  ∑ v, f v N.t

/-- A maximum flow (p. 924): a flow whose value is at least the value of every flow. -/
def IsMaxFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  IsFlow N f ∧ ∀ g : V → V → ℝ, IsFlow N g → value N g ≤ value N f

/-- Residual capacity `r_f(v, w) = c(v, w) - f(v, w)` (p. 924). -/
def residualCap (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  N.c v w - f v w

/-- `(v, w)` is a residual edge, i.e. an edge of the residual graph `G_f`, iff
`r_f(v, w) > 0` (p. 924). -/
def IsResidualEdge (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  0 < residualCap N f v w

/-- `ResidualReachable N f v w`: `w` is reachable from `v` in the residual graph `G_f`
(a path of zero or more residual edges from `v` to `w`). -/
def ResidualReachable (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  Relation.ReflTransGen (IsResidualEdge N f) v w

end GoldbergTarjan.Generic
