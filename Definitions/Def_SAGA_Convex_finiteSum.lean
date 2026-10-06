import Mathlib

namespace SAGA.Convex

/-- The finite-sum objective `f(x) = (1/n) ∑ᵢ fᵢ(x)` (Defazio–Bach–Lacoste-Julien, p. 1),
with the components indexed by `Fin n`. -/
noncomputable def fAvg {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i x

/-- The average `f′(x) = (1/n) ∑ᵢ f′ᵢ(x)` of the given component gradients `f′ᵢ`. -/
noncomputable def gradAvg {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (1 / (n : ℝ)) • ∑ i, f' i x

end SAGA.Convex
