import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.Shared

/-- The cubic regularization of the second-order Taylor model of `f` at `x` (Nesterov–Polyak 2006,
p. 181, Eq. (2.4)), as a function of the trial point `y`:
`⟨f′(x), y − x⟩ + ½⟨f″(x)(y − x), y − x⟩ + (M/6)‖y − x‖³`.
Here `g x` plays the role of `f′(x)` and `H x` of `f″(x)`. -/
noncomputable def cubicModel {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪g x, y - x⟫ + (1 / 2) * ⟪H x (y - x), y - x⟫ + M / 6 * ‖y - x‖ ^ 3

end CubicNewton.Shared
