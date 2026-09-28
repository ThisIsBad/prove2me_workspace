import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_SmoothedFunction
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

/-- Lemma 6.7 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
p. 110, PDF p. 132). Fix `δ > 0`. Let `f̂_δ` be as defined in (6.4) (`SmoothedFunction`), and let
`u` be a uniformly drawn unit vector `u ∼ S`. Then `E_{u ∈ S}[f(x + δu) u] = (δ/n) ∇f̂_δ(x)`. -/
theorem spherical_gradient_estimator_identity
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ) (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n))
    (U : Ω → EuclideanSpace ℝ (Fin n)) (hU : IsUniformOnUnitSphere Prob U)
    (grad : EuclideanSpace ℝ (Fin n)) (hgrad : HasGradientAt (SmoothedFunction f δ) grad x)
    (hint : Integrable (fun ω => f (x + δ • U ω) • U ω) Prob) :
    (∫ ω, f (x + δ • U ω) • U ω ∂Prob) = (δ / n) • grad := by sorry

end OnlineConvexOpt.BanditConvex
