import Mathlib

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

/-- `R` is nonexpansive (1-Lipschitz): `‖R x - R y‖ ≤ ‖x - y‖`. -/
def IsNonexpansive {H : Type*} [NormedAddCommGroup H] (R : H → H) : Prop :=
  ∀ x y : H, ‖R x - R y‖ ≤ ‖x - y‖

/-- `T` is firmly nonexpansive: `‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
def IsFirmlyNonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ ⟪T x - T y, x - y⟫_ℝ

/-- `T` is `α`-averaged: `α ∈ (0, 1)` and `T = (1 - α) I + α R` for some nonexpansive `R`. -/
def IsAveraged {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (T : H → H) : Prop :=
  0 < α ∧ α < 1 ∧ ∃ R : H → H, IsNonexpansive R ∧ ∀ x : H, T x = (1 - α) • x + α • R x

end ThreeOpSplitting.Convergence
