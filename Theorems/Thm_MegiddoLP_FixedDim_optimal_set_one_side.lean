import Mathlib
import Definitions.Def_Polyhedron

/-!
Megiddo, J. ACM 31 (1984), §4 p. 123: if a hyperplane contains no optimal point of a linear
program, all optimal points lie on one side of it (convexity of the optimal set).
-/

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

/-- **Optimal points on one side.** For the program `minimize cᵀx subject to Ax ≥ b` and a
hyperplane `{a ⬝ᵥ x = β}` containing no optimal solution, either every optimal solution has
`a ⬝ᵥ x < β` or every optimal solution has `a ⬝ᵥ x > β`. -/
theorem optimal_set_one_side {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (c a : Fin d → ℝ) (β : ℝ)
    (hmiss : ∀ x, IsLpOptimal c (polyhedron A b) x → a ⬝ᵥ x ≠ β) :
    (∀ x, IsLpOptimal c (polyhedron A b) x → a ⬝ᵥ x < β) ∨
    (∀ x, IsLpOptimal c (polyhedron A b) x → β < a ⬝ᵥ x) := by sorry

end MegiddoLP.FixedDim
