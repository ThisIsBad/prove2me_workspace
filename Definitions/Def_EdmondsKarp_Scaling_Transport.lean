import Mathlib

namespace EdmondsKarp.Scaling

/-- The nodes of the network of Figure 1 (Edmonds–Karp 1972, p. 259): the source `s`, the sink `t`,
the supply nodes `s_1, …, s_m` (`src i`) and the demand nodes `t_1, …, t_n` (`dst j`). -/
inductive Node (m n : ℕ) where
  | s : Node m n
  | t : Node m n
  | src : Fin m → Node m n
  | dst : Fin n → Node m n
  deriving DecidableEq

/-- Data of a problem on the network of Figure 1 (§2.2, p. 258): the capacity `a i` of the arc
`(s, s_i)`, the capacity `b j` of the arc `(t_j, t)`, and the cost `d i j` of the arc `(s_i, t_j)`.
The arcs `(s_i, t_j)` and the return arc `(t, s)` have capacity `+∞`; the arcs `(s, s_i)`, `(t_j, t)`
and the return arc have cost `0`. Sign and integrality conditions on the data are stated as
hypotheses where the paper assumes them. -/
structure Transport (m n : ℕ) where
  a : Fin m → ℝ
  b : Fin n → ℝ
  d : Fin m → Fin n → ℝ

/-- A function on the arcs of the network of Figure 1, in the paper's notation (p. 258):
`f0 i = f_{0i} = f(s, s_i)`, `fx i j = f_{ij} = f(s_i, t_j)`, `fz j = f_{j0} = f(t_j, t)`,
and `ret = f(t, s)`, the value on the return arc. -/
structure Flow (m n : ℕ) where
  f0 : Fin m → ℝ
  fx : Fin m → Fin n → ℝ
  fz : Fin n → ℝ
  ret : ℝ

variable {m n : ℕ}

/-- The zero function on the arcs. -/
instance : Zero (Flow m n) := ⟨⟨0, 0, 0, 0⟩⟩

/-- Scalar multiple `c • f` (arcwise); the scaling method uses `2 • f` (p. 260). -/
instance : SMul ℝ (Flow m n) := ⟨fun c x => ⟨c • x.f0, c • x.fx, c • x.fz, c * x.ret⟩⟩

/-- A flow in the network of Figure 1 (§1.1, p. 249): nonnegative on every arc including the return
arc, at most the capacity on the finite-capacity arcs `(s, s_i)` and `(t_j, t)`, and conserving
flow (outflow minus inflow equals zero) at every node `s`, `s_i`, `t_j`, `t`. -/
def IsFlow (T : Transport m n) (x : Flow m n) : Prop :=
  (∀ i, 0 ≤ x.f0 i) ∧ (∀ i j, 0 ≤ x.fx i j) ∧ (∀ j, 0 ≤ x.fz j) ∧ 0 ≤ x.ret ∧
  (∀ i, x.f0 i ≤ T.a i) ∧ (∀ j, x.fz j ≤ T.b j) ∧
  (∑ i, x.f0 i) - x.ret = 0 ∧
  (∀ i, (∑ j, x.fx i j) - x.f0 i = 0) ∧
  (∀ j, x.fz j - ∑ i, x.fx i j = 0) ∧
  x.ret - ∑ j, x.fz j = 0

/-- A maximum flow (§1.1, p. 249): a flow whose return-arc value is at least that of every flow. -/
def IsMaxFlow (T : Transport m n) (x : Flow m n) : Prop :=
  IsFlow T x ∧ ∀ y : Flow m n, IsFlow T y → y.ret ≤ x.ret

/-- The cost of a flow (§2.1, p. 255): `∑_{(u,v) ∈ A} d(u,v) f(u,v)`; only the arcs `(s_i, t_j)`
have nonzero cost in the network of Figure 1. -/
def cost (T : Transport m n) (x : Flow m n) : ℝ :=
  ∑ i, ∑ j, T.d i j * x.fx i j

/-- An extreme flow (§2.1, p. 255): a flow of minimum cost among the flows with the same value
`f(t, s)`. -/
def IsExtreme (T : Transport m n) (x : Flow m n) : Prop :=
  IsFlow T x ∧ ∀ y : Flow m n, IsFlow T y → y.ret = x.ret → cost T x ≤ cost T y

/-- A pseudo-extreme flow (§2.2, p. 259): a flow for which there exist real numbers `u_i`, `v_j`
satisfying (5a) `u_i - v_j + d_ij ≥ 0` for all `i, j`, and (5b) `u_i - v_j + d_ij > 0 ⇒ f_ij = 0`. -/
def IsPseudoExtreme (T : Transport m n) (x : Flow m n) : Prop :=
  IsFlow T x ∧ ∃ (u : Fin m → ℝ) (v : Fin n → ℝ),
    (∀ i j, 0 ≤ u i - v j + T.d i j) ∧
    (∀ i j, 0 < u i - v j + T.d i j → x.fx i j = 0)

end EdmondsKarp.Scaling
