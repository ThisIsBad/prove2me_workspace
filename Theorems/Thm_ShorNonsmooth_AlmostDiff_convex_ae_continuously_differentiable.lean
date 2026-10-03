import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, proof of Theorem 1.15, first sentence (Rademacher's theorem, cited from
[12]): a convex function on `E_n` is almost everywhere continuously differentiable, i.e. it is
differentiable at almost every point (Lebesgue measure), and its gradient is continuous on the set
of points where it is differentiable. -/
theorem convex_ae_continuously_differentiable {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
        DifferentiableAt ℝ f x) ∧
      ContinuousOn (gradient f) {x | DifferentiableAt ℝ f x} := by sorry

end ShorNonsmooth.AlmostDiff

