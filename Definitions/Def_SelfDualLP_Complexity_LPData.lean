import Mathlib
import Definitions.Def_LinearOptimization_DualLP

open Matrix

namespace SelfDualLP.Complexity

/-! The standard-form linear program (LP) `minimize cᵀx subject to Ax = b, x ≥ 0` and its dual
(LD) `maximize bᵀy subject to Aᵀy ≤ c`, with dual slacks `s = c − Aᵀy`
(Ye–Todd–Mizuno 1994, §1, p. 53), built on the published general-form LP
`LinearOptimization.stdFormLP` and its standard-form dual feasible set
`LinearOptimization.dualFeasibleStd`. The data `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, `c ∈ ℝ^n` are real. -/

/-- `x` is feasible for (LP): `Ax = b` and `x ≥ 0`. -/
def LPFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c)

/-- (LP) is feasible: its constraints are consistent. -/
def LPIsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Prop :=
  ∃ x, LPFeasible A b c x

/-- `x` is an optimal solution of (LP): it is feasible and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def LPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  LinearOptimization.IsLpOptimal c
    (LinearOptimization.generalFeasibleSet (LinearOptimization.stdFormLP A b c)) x

/-- (LP) has a solution: it has an optimal solution. -/
def LPHasSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Prop :=
  ∃ x, LPOptimal A b c x

/-- `(y, s)` is feasible for (LD): `Aᵀy ≤ c` and `s = c − Aᵀy` is its dual slack. -/
def LDFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  y ∈ LinearOptimization.dualFeasibleStd A c ∧ s = c - Aᵀ *ᵥ y

/-- (LD) is feasible: some `y` has `Aᵀy ≤ c`. -/
def LDIsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  (LinearOptimization.dualFeasibleStd A c).Nonempty

/-- `(y, s)` is an optimal solution of (LD): `y` maximizes `bᵀy` over `{y : Aᵀy ≤ c}` and
`s = c − Aᵀy` is its dual slack. -/
def LDOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  LinearOptimization.IsLpDualOptimal b (LinearOptimization.dualFeasibleStd A c) y ∧
    s = c - Aᵀ *ᵥ y

end SelfDualLP.Complexity
