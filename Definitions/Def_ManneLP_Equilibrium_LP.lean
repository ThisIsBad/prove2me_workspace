import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model

namespace ManneLP.Equilibrium

/-- `Σⱼ xₜⱼ`, the left side of (8.0)–(8.T), and `yₜ` of (3). -/
def marginal (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ actions M t, x (t, j)

/-- The right side of (7)/(8.0): `Σ_{i,j,n : i+j−n ≦ 0} pₙ xᵢⱼ`. -/
noncomputable def rhsZero (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ,
    if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) ≤ 0 then M.p n * x a else 0

/-- The right side of (7)/(8.t), `t = 1, …, T`: `Σ_{i,j,n : i+j−n = t} pₙ xᵢⱼ`. -/
noncomputable def rhsPos (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ a ∈ M.A, ∑' n : ℕ,
    if (a.1 : ℤ) + (a.2 : ℤ) - (n : ℤ) = (t : ℤ) then M.p n * x a else 0

/-- Equation (8.0). -/
def Eq80 (M : Model) (x : ℕ × ℕ → ℝ) : Prop :=
  marginal M x 0 = rhsZero M x

/-- Equation (8.t). -/
def Eq8t (M : Model) (x : ℕ × ℕ → ℝ) (t : ℕ) : Prop :=
  marginal M x t = rhsPos M x t

/-- The constraint set of Manne's linear program (§4, last paragraph): `xᵢⱼ ≧ 0` on the admissible
pairs, (4) `Σ xᵢⱼ = 1`, and (8.1)–(8.T). Equation (8.0) is deliberately not included. -/
def IsLPFeasible (M : Model) (x : ℕ × ℕ → ℝ) : Prop :=
  (∀ a ∈ M.A, 0 ≤ x a) ∧ ∑ a ∈ M.A, x a = 1 ∧ ∀ t, 1 ≤ t → t ≤ M.T → Eq8t M x t

/-- The cost coefficient (10): `cᵢⱼ = C₁(i) + C₂(j) + Σₙ pₙ C₃(n − i − j)`. -/
noncomputable def costCoeff (M : Model) (i j : ℕ) : ℝ :=
  M.C₁ i + M.C₂ j + ∑' n : ℕ, M.p n * M.C₃ ((n : ℤ) - (i : ℤ) - (j : ℤ))

/-- The objective (9): `Σ_{i,j} cᵢⱼ xᵢⱼ`. -/
noncomputable def lpObj (M : Model) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ a ∈ M.A, costCoeff M a.1 a.2 * x a

/-- `x` is an optimal solution of the linear program: feasible, and of least objective (9) among
feasible points. -/
def IsLPOptimal (M : Model) (x : ℕ × ℕ → ℝ) : Prop :=
  IsLPFeasible M x ∧ ∀ x', IsLPFeasible M x' → lpObj M x ≤ lpObj M x'

/-- The decoded equilibrium distribution (3): `yᵢ = Σⱼ xᵢⱼ`. -/
def decodeDist (M : Model) (x : ℕ × ℕ → ℝ) : ℕ → ℝ :=
  fun i => marginal M x i

/-- The decoded decision rule (§3, N.B.): `q(j | i) = xᵢⱼ / Σⱼ xᵢⱼ` on admissible pairs when
`Σⱼ xᵢⱼ ≠ 0`; at a stock level with `Σⱼ xᵢⱼ = 0` (never visited in equilibrium) the default pure
action "produce nothing" (`j = 0`) is used. -/
noncomputable def decodeRule (M : Model) (x : ℕ × ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun i j =>
    if (i, j) ∈ M.A then
      (if marginal M x i ≠ 0 then x (i, j) / marginal M x i else if j = 0 then 1 else 0)
    else 0

end ManneLP.Equilibrium
