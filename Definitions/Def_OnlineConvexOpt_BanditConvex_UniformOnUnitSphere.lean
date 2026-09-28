import Mathlib

namespace OnlineConvexOpt.BanditConvex

open MeasureTheory

/-- `U` is uniformly distributed on the Euclidean unit sphere `S = {u | ‖u‖ = 1}` in
`EuclideanSpace ℝ (Fin n)` (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 110, PDF p. 132, `u ∼ S` in Lemma 6.7 and Algorithm 23), operationally
characterized, as in the sphere-sampling conventions elsewhere in this workspace, by: `U` lies on
the sphere almost surely, and the law of `U` is invariant under every orthogonal (linear
isometric) transformation of `EuclideanSpace ℝ (Fin n)` — the property that pins down the unique
rotation-invariant probability measure on the sphere, the normalized surface measure the book
calls `S`. -/
def IsUniformOnUnitSphere {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ}
    (U : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ᵐ ω ∂Prob, U ω ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
  (∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
    Measure.map (fun ω => L (U ω)) Prob = Measure.map U Prob)

end OnlineConvexOpt.BanditConvex
