import Mathlib

namespace CycleCanceling.MinMean

/-- A circulation network (Goldberg–Tarjan 1989, §2, p. 875): a directed graph `G = (V, E)` on a
finite vertex type `V`, whose arc set `E` is symmetric (`(v, w) ∈ E ↔ (w, v) ∈ E`), with a real
capacity `u (v, w)` and a real cost `c (v, w)` on every arc; the cost is antisymmetric on `E`.
Values of `u` and `c` off `E` are never read. -/
structure CircNetwork (V : Type*) [Fintype V] [DecidableEq V] where
  /-- the arc set `E` -/
  E : Finset (V × V)
  /-- capacities `u (v, w)` -/
  u : V → V → ℝ
  /-- costs `c (v, w)` -/
  c : V → V → ℝ
  /-- `G` is symmetric -/
  symm : ∀ v w, (v, w) ∈ E ↔ (w, v) ∈ E
  /-- the cost is antisymmetric on `E` -/
  cost_antisymm : ∀ v w, (v, w) ∈ E → c v w = -c w v

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A circulation (§2, p. 876, constraints (1)–(3)): a real function `f` on arcs with
`f (v, w) ≤ u (v, w)` and `f (v, w) = -f (w, v)` for every `(v, w) ∈ E`, and
`∑_{v ∈ E(w)} f (v, w) = 0` for every vertex `w`, where `E(w) = {v | (w, v) ∈ E}`. -/
def IsCirculation (N : CircNetwork V) (f : V → V → ℝ) : Prop :=
  (∀ v w, (v, w) ∈ N.E → f v w ≤ N.u v w) ∧
  (∀ v w, (v, w) ∈ N.E → f v w = -f w v) ∧
  (∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), f v w = 0)

/-- `cost(f) = ½ ∑_{(v,w) ∈ E} c(v, w) f(v, w)` (§2, p. 876). -/
noncomputable def cost (N : CircNetwork V) (f : V → V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a ∈ N.E, N.c a.1 a.2 * f a.1 a.2

/-- A minimum-cost circulation: a circulation whose cost is at most that of every circulation. -/
def IsMinCost (N : CircNetwork V) (f : V → V → ℝ) : Prop :=
  IsCirculation N f ∧ ∀ g, IsCirculation N g → cost N f ≤ cost N g

/-- Residual capacity `u_f(v, w) = u(v, w) - f(v, w)` (p. 876). -/
def resCap (N : CircNetwork V) (f : V → V → ℝ) (v w : V) : ℝ :=
  N.u v w - f v w

/-- The arcs of a cycle given by its vertex list `[v₀, v₁, …, v_{l-1}]`: the consecutive pairs
`(v₀, v₁), …, (v_{l-2}, v_{l-1}), (v_{l-1}, v₀)`. -/
def cycleArcs (Γ : List V) : List (V × V) :=
  Γ.zip (Γ.rotate 1)

/-- A residual cycle (p. 876): a simple cycle (nonempty, no repeated vertex) all of whose arcs are
residual arcs, i.e. arcs of `E` with positive residual capacity. -/
def IsResidualCycle (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) : Prop :=
  Γ ≠ [] ∧ Γ.Nodup ∧ ∀ a ∈ cycleArcs Γ, a ∈ N.E ∧ 0 < resCap N f a.1 a.2

/-- The cost of a cycle: the sum of the costs of its arcs (p. 876). -/
def cycleCost (N : CircNetwork V) (Γ : List V) : ℝ :=
  ((cycleArcs Γ).map (fun a => N.c a.1 a.2)).sum

/-- The mean cost of a cycle: its cost divided by its number of arcs `l = |Γ|` (p. 876). Only
applied to nonempty cycles. -/
noncomputable def meanCost (N : CircNetwork V) (Γ : List V) : ℝ :=
  cycleCost N Γ / (Γ.length : ℝ)

/-- `Γ` is a minimum-mean residual cycle of `f`: a residual cycle whose mean cost is at most the
mean cost of every residual cycle of `f`. -/
def IsMinMeanResidualCycle (N : CircNetwork V) (f : V → V → ℝ) (Γ : List V) : Prop :=
  IsResidualCycle N f Γ ∧ ∀ Γ', IsResidualCycle N f Γ' → meanCost N Γ ≤ meanCost N Γ'

end CycleCanceling.MinMean
