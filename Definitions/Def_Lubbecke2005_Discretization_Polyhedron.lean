import Mathlib

namespace Lubbecke2005.Discretization

/-- The cast of an integer vector `z ∈ ℤⁿ` to the real vector `(z₁, …, zₙ) ∈ ℝⁿ`. -/
def castVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ :=
  fun j => (z j : ℝ)

/-- The polyhedron `P = {𝐱 ∈ ℝⁿ | D𝐱 ⩾ 𝐝, 𝐱 ⩾ 𝟎}` of Theorem 1
(Lübbecke–Desrosiers 2005, §3.3, p. 1011), for an `m × n` matrix `D` and an
`m`-vector `𝐝` with rational entries, cast to `ℝ`. -/
def polyhedronP {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, (d i : ℝ) ≤ ∑ j, (D i j : ℝ) * x j) ∧ ∀ j, 0 ≤ x j}

/-- The set of integer points `X = P ∩ ℤⁿ` of Theorem 1 (§3.3, p. 1011): the points
of `P` all of whose coordinates are integers. -/
def integerPoints {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (d : Fin m → ℚ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ polyhedronP D d ∧ ∃ z : Fin n → ℤ, x = castVec z}

/-- The recession cone `{𝐫 ∈ ℝⁿ | D𝐫 ⩾ 𝟎, 𝐫 ⩾ 𝟎}` of `P`. For nonempty `P` it is the set
of directions `𝐫` with `𝐱 + t𝐫 ∈ P` for all `𝐱 ∈ P`, `t ⩾ 0`. -/
def recessionConeP {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) : Set (Fin n → ℝ) :=
  {r | (∀ i, 0 ≤ ∑ j, (D i j : ℝ) * r j) ∧ ∀ j, 0 ≤ r j}

/-- An *integer ray* of `P` (Theorem 1, §3.3, p. 1011): a nonzero integer vector
`𝐰 ∈ ℤⁿ` lying in the recession cone of `P`. Extremality is not required. -/
def IsIntegerRay {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ) (w : Fin n → ℤ) : Prop :=
  w ≠ 0 ∧ castVec w ∈ recessionConeP D

end Lubbecke2005.Discretization
