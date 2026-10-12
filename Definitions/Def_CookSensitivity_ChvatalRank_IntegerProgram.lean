import Mathlib

namespace CookSensitivity.ChvatalRank

open Matrix

/-- A rational vector is integral when every coordinate is an integer. -/
def IsIntegral {n : ℕ} (x : Fin n → ℚ) : Prop :=
  ∀ i, ∃ k : ℤ, x i = k

/-- The polyhedron `{x ∈ ℚⁿ : Ax ≤ b}` of an integral `m × n` matrix `A` and a rational
right-hand side `b` (componentwise order). -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) : Set (Fin n → ℚ) :=
  {x | (A.map (Int.cast : ℤ → ℚ)) *ᵥ x ≤ b}

/-- `x` is an optimal solution to the linear program `max {wx : Ax ≤ b}`. -/
def IsLPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (x : Fin n → ℚ) : Prop :=
  x ∈ polyhedron A b ∧ ∀ y ∈ polyhedron A b, w ⬝ᵥ y ≤ w ⬝ᵥ x

/-- `z` is an optimal solution to the integer program `max {wx : Ax ≤ b, x integral}`. -/
def IsIPOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (z : Fin n → ℚ) : Prop :=
  IsIntegral z ∧ z ∈ polyhedron A b ∧
    ∀ y ∈ polyhedron A b, IsIntegral y → w ⬝ᵥ y ≤ w ⬝ᵥ z

/-- `P ⊆ ℚⁿ` is a (rational) polyhedron: the solution set of finitely many rational linear
inequalities `Dx ≤ d` (`k = 0` rows gives `ℚⁿ`). -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℚ)) : Prop :=
  ∃ (k : ℕ) (D : Matrix (Fin k) (Fin n) ℚ) (d : Fin k → ℚ), P = {x | D *ᵥ x ≤ d}

/-- The integer hull `S_I`: the convex hull (over `ℚ`) of the integral vectors in `S`. -/
def integerHull {n : ℕ} (S : Set (Fin n → ℚ)) : Set (Fin n → ℚ) :=
  convexHull ℚ {x | x ∈ S ∧ IsIntegral x}

end CookSensitivity.ChvatalRank
