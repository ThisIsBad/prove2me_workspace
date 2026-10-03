import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 17, Definition: `f : E_n → ℝ` is **almost differentiable** if
(a) in any bounded set it satisfies the Lipschitz condition (the constant may depend on the set);
(b) it is differentiable almost everywhere (Lebesgue measure on `E_n`);
(c) its gradient is continuous on its domain `M`, the set of points where `f` is differentiable
(continuity of the restriction of `∇f` to `M`). -/
def AlmostDifferentiable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ S : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded S →
      ∃ L : NNReal, LipschitzOnWith L f S) ∧
  (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      DifferentiableAt ℝ f x) ∧
  ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x}

end ShorNonsmooth.AlmostDiff
