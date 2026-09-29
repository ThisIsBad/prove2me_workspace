import Mathlib

namespace MurtyKabadi.Reduction

open Matrix

/-- The quadratic form `Q(x) = xᵀDx` of a square real matrix `D`
(Murty–Kabadi 1987, p. 121, QP (7)). -/
def Q {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (D *ᵥ x)

/-- `D` is copositive: `xᵀDx ≥ 0` for all `x ≥ 0` (p. 121). -/
def Copositive {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, 0 ≤ x → 0 ≤ Q D x

/-- Problem 1 (p. 122): is `x = 0` not a local minimum of `Q` on `{x ≥ 0}` (QP (7))? -/
def Problem1 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ IsLocalMinOn (Q D) {x : ι → ℝ | 0 ≤ x} 0

/-- Problem 2 (p. 122): is `Q` not bounded below on the feasible set `{x ≥ 0}` of (7)? -/
def Problem2 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ BddBelow (Q D '' {x : ι → ℝ | 0 ≤ x})

/-- Problem 3 (p. 123): is there an `x ≥ 0` with `Q(x) < 0`? -/
def Problem3 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ∃ x : ι → ℝ, 0 ≤ x ∧ Q D x < 0

/-- Problem 4 (p. 123): given `a₀`, is there an `x` with `eᵀx = a₀`, `x ≥ 0` and `Q(x) < 0`? -/
def Problem4 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (a0 : ℝ) : Prop :=
  ∃ x : ι → ℝ, ∑ i, x i = a0 ∧ 0 ≤ x ∧ Q D x < 0

/-- The objective of the unconstrained QP (15) (p. 126):
`h(u) = (u₁², …, u_n²) D (u₁², …, u_n²)ᵀ`. -/
def h {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ :=
  Q D (fun i => u i ^ 2)

/-- Problem 11 (p. 126): is `u = 0` not a local minimum of (15)? -/
def Problem11 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ IsLocalMin (h D) 0

/-- Problem 12 (p. 126): is `h` not bounded below? -/
def Problem12 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ BddBelow (Set.range (h D))

end MurtyKabadi.Reduction
