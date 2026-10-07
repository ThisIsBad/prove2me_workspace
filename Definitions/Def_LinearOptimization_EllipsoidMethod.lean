import Mathlib.Data.Real.Sqrt
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_Polyhedron

/-!
The ellipsoid method as an iteration predicate.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, Chapter 8 — the boxed algorithm on p. 371, whose
update step is the Theorem 8.1 (p. 366) construction: given the current
ellipsoid `E(z, D)` and a nonzero vector `a`,

- new center `z̄ = z + (1/(n+1)) · Da / √(a'Da)`,
- new matrix `D̄ = (n²/(n²−1)) · (D − (2/(n+1)) · Daa'D / (a'Da))`.

The algorithm (p. 371): given `P = {x | aᵢ'x ≥ bᵢ, i = 1, …, m}`, at
iteration `t` with current ellipsoid `E(x_t, D_t)`, if `x_t ∉ P` pick a
violated constraint `aᵢ'x_t < bᵢ` and produce `E(x_{t+1}, D_{t+1})` by the
update above with `a = aᵢ` (the halfspace `H_t = {x | aᵢ'x ≥ aᵢ'x_t}`
retains all of `P ∩ E_t`); if `x_t ∈ P` stop ("P is nonempty"); after `t*`
iterations stop ("P is empty").

Design (series architecture decision — algorithms are predicates, not
programs): `IsEllipsoidStep` relates `(x_t, D_t)` to `(x_{t+1}, D_{t+1})`
through SOME violated row, and `IsEllipsoidRun` requires an admissible
step at every `t < T` at which the current center is infeasible — so the
correctness theorem (Theorem 8.2) quantifies over every admissible run and
every rule for choosing the violated constraint. Positive definiteness of
`D_t` propagates by Theorem 8.1; the `√·` and the scalar inverses are
Lean-total (junk values only arise outside the guarded statements). The
factor `n²/(n²−1)` forces the `2 ≤ n` hypothesis carried by the theorems.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Theorem 8.1 / algorithm step (d) (pp. 366, 371).** The updated
center `z̄ = z + (1/(n+1)) · Da / √(a'Da)`. -/
noncomputable def ellipsoidUpdateCenter {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Fin n → ℝ :=
  z + ((1 : ℝ) / (n + 1)) • (Real.sqrt (a ⬝ᵥ D.mulVec a))⁻¹ • D.mulVec a

/-- **Bertsimas & Tsitsiklis, Theorem 8.1 / algorithm step (d) (pp. 366, 371).** The updated
matrix `D̄ = (n²/(n²−1)) · (D − (2/(n+1)) · Daa'D / (a'Da))`; `Daa'D` is
the matrix product `D * (aa') * D` with `aa' = vecMulVec a a`. -/
noncomputable def ellipsoidUpdateMatrix {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (D - ((2 : ℝ) / (n + 1)) • (a ⬝ᵥ D.mulVec a)⁻¹ •
      (D * vecMulVec a a * D))

/-- **Bertsimas & Tsitsiklis, p. 371, main iteration steps (c)–(d).** One admissible step of
the ellipsoid method for `P = {x | Ax ≥ b}`: SOME violated constraint
`aᵢ'x < bᵢ` is found, and the next center/matrix are produced by the
Theorem 8.1 update with `a = aᵢ` — covering every rule for choosing the
violated constraint. -/
def IsEllipsoidStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (x' : Fin n → ℝ) (D' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ i : Fin m, A i ⬝ᵥ x < b i ∧
    x' = ellipsoidUpdateCenter x D (A i) ∧
    D' = ellipsoidUpdateMatrix D (A i)

/-- **Bertsimas & Tsitsiklis, p. 371 (the boxed algorithm as a run predicate).** The sequences
`(x_t, D_t)` form an admissible run of the ellipsoid method on
`P = {x | Ax ≥ b}` up to time `T`: at every `t < T` whose center is
infeasible, the next iterate is produced by an admissible step (steps
(c)–(d)); once some `x_t ∈ P` the algorithm has stopped ("P is nonempty")
and the run is unconstrained afterwards. -/
def IsEllipsoidRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : ℕ → Fin n → ℝ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (T : ℕ) : Prop :=
  ∀ t < T, x t ∉ polyhedron A b →
    IsEllipsoidStep A b (x t) (D t) (x (t + 1)) (D (t + 1))

end LinearOptimization
