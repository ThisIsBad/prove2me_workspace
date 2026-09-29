import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.OnlineBoosting

/-- The smoothing operator `S_δ[f](x) = E_{v∈B}[f(x+δv)]` (Hazan, *Introduction to Online
Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Lemma 2.8, reused p. 199, PDF p. 221).
Redeclared here (not imported) since Chapter II's own smoothing operator is not yet a published
series definition, and matches `BanditConvex.SmoothedFunction` (Chunk 06, also unpublished) in
content; see `MODERATION_NOTES.md`. -/
noncomputable def SmoothedFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal⁻¹ *
    ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f (x + δ • v)

/-- Definition 12.2, the `(K, κ, δ)`-extension (p. 199, PDF p. 221):
`X_{K,κ,δ}[f] = S_δ[f + κ·Dist(·,K)]`, where `Dist(x,K) = min_{y∈K}‖y-x‖` (Mathlib's
`Metric.infDist`, matching the book's own definition exactly). -/
noncomputable def Extension {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (κ δ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  SmoothedFunction (fun y => f y + κ * Metric.infDist y K) δ x

end OnlineConvexOpt.OnlineBoosting
