import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Ellipsoids, affine transformations, and full-dimensional sets.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **Definition 8.4 (p. 364).** An `n × n` symmetric matrix `D` is positive
  definite if `x'Dx > 0` for every nonzero `x` — this is Mathlib's
  `Matrix.PosDef` (whose `IsHermitian` component, over `ℝ`, is exactly
  symmetry); no custom Def is minted (Mathlib-first).
- **Definition 8.5 (p. 364).** A set of the form
  `E = E(z, D) = {x ∈ ℝⁿ | (x − z)'D⁻¹(x − z) ≤ 1}`, with `D` an `n × n`
  positive definite symmetric matrix, is an *ellipsoid* with center `z`.
  For `r > 0`, `E(z, r²I) = {x | ‖x − z‖ ≤ r}` is the ball centered at `z`
  with radius `r` (the def `ellipsoidBall` below packages `E(z, r²I)`).
- **Definition 8.6 (p. 364).** For `S : ℝⁿ → ℝⁿ` of the form `S(x) = Dx + b`
  with `D` an `n × n` nonsingular matrix and `b ∈ ℝⁿ`, `S` is an *affine
  transformation*, with image `S(L) = {y | y = Dx + b for some x ∈ L}`.
- **Volume (p. 365).** `Vol(L) = ∫_{x ∈ L} dx` — Mathlib's Lebesgue
  `MeasureTheory.volume` on `Fin n → ℝ` (the pi measure); no custom Def.
- **Definition 8.7 (p. 370).** A polyhedron is *full-dimensional* if it has
  positive volume. (Stated for an arbitrary subset of `ℝⁿ`.)

The `D⁻¹` in `ellipsoid` is Mathlib's `Matrix.inv` (junk `D⁻¹ = 0` for
singular `D`); every theorem using `ellipsoid` carries a `Matrix.PosDef`
guard, per the series faithfulness rules.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 8.5 (p. 364).** The ellipsoid with center `z` and
(positive definite symmetric) shape matrix `D`:
`E(z, D) = {x | (x − z)'D⁻¹(x − z) ≤ 1}`. (`D⁻¹` is Mathlib matrix
inverse; statements guard `D` with `Matrix.PosDef`.) -/
def ellipsoid {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  {x | (x - z) ⬝ᵥ D⁻¹.mulVec (x - z) ≤ 1}

/-- **Bertsimas & Tsitsiklis, Definition 8.5 (p. 364), ball case.** `E(z, r²I)`, the ball
centered at `z` of radius `r` (for `r > 0` it equals
`{x | ‖x − z‖ ≤ r}`). -/
def ellipsoidBall {n : ℕ} (z : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  ellipsoid z (r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))

/-- **Bertsimas & Tsitsiklis, Definition 8.6 (p. 364).** The image `S(L)` of `L ⊆ ℝⁿ` under the
affine transformation `S(x) = Dx + b` (`D` nonsingular in the book's
definition; the nonsingularity hypothesis appears in the statements that
need it, e.g. Lemma 8.1's volume scaling). -/
def affineTransformImage {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (L : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∃ x ∈ L, y = D.mulVec x + b}

/-- **Bertsimas & Tsitsiklis, Definition 8.7 (p. 370).** A set (in particular, a polyhedron) is
*full-dimensional* if it has positive (Lebesgue) volume. -/
def IsFullDimensional {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  0 < MeasureTheory.volume S

end LinearOptimization
