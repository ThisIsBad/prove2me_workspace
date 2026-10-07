import Mathlib

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `max V = max_j v_j` of a vector with finitely many, and at least one, components
(Robinson 1951, p. 296). The maximum is attained. -/
noncomputable def vmax [Nonempty ι] (w : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty w

/-- `min V = min_j v_j` of a vector with finitely many, and at least one, components
(Robinson 1951, p. 296). The minimum is attained. -/
noncomputable def vmin [Nonempty ι] (w : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty w

/-- Definition 1 (Robinson 1951, pp. 296–297): `(U, V)` is a vector system for the `m × n` matrix
`A`. Rows are indexed by `ι` (m of them), columns by `κ` (n of them). `U t : κ → ℝ` is
n-dimensional and is increased by a row `A i = A_{i·}`; `V t : ι → ℝ` is m-dimensional and is
increased by a column `fun k => A k j = A_{·j}`. At each step `t` the row `i` maximizes `V t` and
the column `j` minimizes `U t`; ties may be broken arbitrarily, step by step. -/
def IsVectorSystem [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) : Prop :=
  vmin (U 0) = vmax (V 0) ∧
  ∀ t, ∃ i j, V t i = vmax (V t) ∧ U t j = vmin (U t) ∧
    U (t + 1) = U t + A i ∧ V (t + 1) = V t + fun k => A k j

/-- The alternate notion of vector system (Robinson 1951, p. 297): as in Definition 1, except
that the column `j` minimizes the updated vector `U (t + 1)`. -/
def IsAltVectorSystem [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) : Prop :=
  vmin (U 0) = vmax (V 0) ∧
  ∀ t, ∃ i j, V t i = vmax (V t) ∧ U (t + 1) = U t + A i ∧
    U (t + 1) j = vmin (U (t + 1)) ∧ V (t + 1) = V t + fun k => A k j

/-- Definition 2, rows (Robinson 1951, p. 298): row `i` is eligible in the interval `(t, t')`,
i.e. `v_i(t₁) = max V(t₁)` for some `t ≤ t₁ ≤ t'`. -/
def RowEligible [Nonempty ι] (V : ℕ → ι → ℝ) (i : ι) (t t' : ℕ) : Prop :=
  ∃ t₁, t ≤ t₁ ∧ t₁ ≤ t' ∧ V t₁ i = vmax (V t₁)

/-- Definition 2, columns (Robinson 1951, p. 298): column `j` is eligible in the interval
`(t, t')`, i.e. `u_j(t₂) = min U(t₂)` for some `t ≤ t₂ ≤ t'`. -/
def ColEligible [Nonempty κ] (U : ℕ → κ → ℝ) (j : κ) (t t' : ℕ) : Prop :=
  ∃ t₂, t ≤ t₂ ∧ t₂ ≤ t' ∧ U t₂ j = vmin (U t₂)

/-- A solution `(X, Y)` of the matrix game `A` with value `v` (Robinson 1951, p. 296): `x`, `y` are
probability vectors and equality holds in (1),
`min_j Σ_i a_ij x_i = v = max_i Σ_j a_ij y_j`. -/
def IsSolution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) :
    Prop :=
  x ∈ stdSimplex ℝ ι ∧ y ∈ stdSimplex ℝ κ ∧
  vmin (fun j => ∑ i, A i j * x i) = v ∧ vmax (fun i => ∑ j, A i j * y j) = v

end RobinsonFP.Convergence
