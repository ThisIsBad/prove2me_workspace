import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph

namespace SingleMachinePrec.Framework

variable {N : Type*}

/-- Feasibility for [CS-LP], the linear relaxation of [CS-IP] (p. 656), read as the vertex cover
LP of `G^S_P`: one variable `x_u ∈ [0, 1]` per incomparable pair, and `x_u + x_v ≥ 1` for every
edge `uv` of `G^S_P` (these edges are the constraints (1)–(3)). -/
def IsCSLPFeasible (S : Instance N) (x : IncPair S.P → ℝ) : Prop :=
  (∀ u, 0 ≤ x u ∧ x u ≤ 1) ∧ ∀ u v, (vertexCoverGraph S.P).Adj u v → 1 ≤ x u + x v

/-- The variable part `∑_{(i,j)} p_i w_j x_{(i,j)}` of the [CS-LP] objective; the constant
`∑_j p_j w_j + ∑_{(i,j) ∈ P} p_i w_j` of [CS-IP] is dropped (it does not depend on `x`). -/
noncomputable def csLPValue [Fintype N] (S : Instance N) (x : IncPair S.P → ℝ) : ℝ :=
  ∑ u, vertexWeight S u * x u

/-- `x` is an optimal solution of [CS-LP]. -/
def IsCSLPOptimal [Fintype N] (S : Instance N) (x : IncPair S.P → ℝ) : Prop :=
  IsCSLPFeasible S x ∧ ∀ y, IsCSLPFeasible S y → csLPValue S x ≤ csLPValue S y

/-- `x` is half-integral: every value lies in `{0, 1/2, 1}`. -/
def IsHalfIntegral {P : N → N → Prop} (x : IncPair P → ℝ) : Prop :=
  ∀ u, x u = 0 ∨ x u = 1 / 2 ∨ x u = 1

open Classical in
/-- `V_a = {u : x_u = a}` (p. 659), used for `a ∈ {0, 1/2, 1}`. -/
noncomputable def levelSet [Fintype N] {P : N → N → Prop} (x : IncPair P → ℝ) (a : ℝ) :
    Finset (IncPair P) :=
  Finset.univ.filter (fun u => x u = a)

open Classical in
/-- `I_{1/2}` for a linear extension `L` (p. 659): the incomparable pairs of `V_{1/2}` that `L`
reverses. -/
noncomputable def reversedHalf [Fintype N] {P : N → N → Prop} (x : IncPair P → ℝ)
    (L : LinearExtension P) : Finset (IncPair P) :=
  (levelSet x (1 / 2)).filter (fun u => L.Reverses u)

/-- The cover `V_1 ∪ C` with `C = V_{1/2} \ I_{1/2}` that the proof of Theorem 5.1 (p. 659)
builds from a half-integral [CS-LP] solution `x` and a linear extension `L`. -/
noncomputable def roundedCover [Fintype N] [DecidableEq N] {P : N → N → Prop}
    (x : IncPair P → ℝ) (L : LinearExtension P) : Finset (IncPair P) :=
  levelSet x 1 ∪ (levelSet x (1 / 2) \ reversedHalf x L)

end SingleMachinePrec.Framework
