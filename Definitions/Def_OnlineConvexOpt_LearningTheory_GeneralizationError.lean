import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

/-- The generalization error of a hypothesis `h : E → X → ℝ` (Hazan, *Introduction to Online
Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 152, PDF p. 174):
`error(h) = E_{(x,y)∼D}[ℓ(h(x), y)]`, the expected loss of `h`'s predictions against a
distribution `D` on labeled examples. Predictions are parametrized: `pred hparam x` is the
real-valued prediction of the hypothesis identified by `hparam ∈ E` on input `x` (generalizing
the book's `hw(x) = wᵀx`, p. 155). -/
noncomputable def GeneralizationError {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ) (hparam : E) : ℝ :=
  ∫ p, ℓ (pred hparam p.1) p.2 ∂D

/-- The generalization error under the zero-one loss for a `Bool`-labeled concept
(p. 152, PDF p. 174, and used throughout §9.1.2's No Free Lunch theorem): `error(h) =
Pr_{(x,y)∼D}[h(x) ≠ y]`. -/
noncomputable def GeneralizationErrorZeroOne {X : Type*} [MeasurableSpace X]
    (D : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  (D {p : X × Bool | h p.1 ≠ p.2}).toReal

end OnlineConvexOpt.LearningTheory
