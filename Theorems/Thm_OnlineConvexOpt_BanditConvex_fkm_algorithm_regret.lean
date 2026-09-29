import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

/-- Theorem 6.9 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 113, PDF p. 135). Algorithm 23 (the FKM algorithm) with parameters
`η = D / (n T^{3/4})`, `δ = 1 / T^{1/4}` guarantees the following expected regret bound:
`Σ_{t=1}^T E[f_t(y_t)] - min_{x ∈ K} Σ_{t=1}^T f_t(x) ≤ 9 n D G T^{3/4} = O(T^{3/4})`.

`K ⊆ EuclideanSpace ℝ (Fin n)` contains the unit ball centered at `0` (p. 112, PDF p. 134), is
convex with diameter `≤ D`, and carries `G`-Lipschitz cost functions `f_t` bounded by `1` in
absolute value on `K` (the chapter's standing simplifying assumptions for Algorithm 23, stated
here as explicit hypotheses). `Kδ` is the shrunk Minkowski set `{z | (1 - δ)⁻¹ z ∈ K}` (p. 112,
PDF p. 134) that Algorithm 23 projects onto, kept as its own object (never conflated with `K`).
`u_t ∼ S` is the round-`t` uniformly drawn unit vector, `y_t = x_t + δ u_t` the played point, and
`g_t = (n/δ) f_t(y_t) u_t` the gradient estimate driving the projected-gradient update
`x_{t+1} = Π_{Kδ}[x_t - η g_t]` of line 5 of Algorithm 23 (reusing `IsMetricProjection` from
Chapter III's `Protocol`). -/
theorem fkm_algorithm_regret
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K Kδ : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hKball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (T : ℕ) (hT : 1 ≤ T)
    (η δ : ℝ) (hη : η = D / ((n : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)))
    (hδ : δ = 1 / (T : ℝ) ^ (1 / 4 : ℝ))
    (hKδ : ∀ z : EuclideanSpace ℝ (Fin n), z ∈ Kδ ↔ (1 - δ)⁻¹ • z ∈ K)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfbdd : ∀ t, ∀ x ∈ K, |f t x| ≤ 1)
    (x y u g : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = 0)
    (hu : ∀ t, IsUniformOnUnitSphere Prob (u t))
    (hy : ∀ t ω, y t ω = x t ω + δ • u t ω)
    (hg : ∀ t ω, g t ω = ((n : ℝ) / δ * f t (y t ω)) • u t ω)
    (hstep : ∀ t ω,
      OnlineConvexOpt.FirstOrder.IsMetricProjection Kδ (x t ω - η • g t ω) (x (t + 1) ω))
    (hint : ∀ t, Integrable (fun ω => f t (y t ω)) Prob) :
    (∑ t ∈ Finset.range T, ∫ ω, f t (y t ω) ∂Prob) - ⨅ z ∈ K, ∑ t ∈ Finset.range T, f t z ≤
      9 * n * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end OnlineConvexOpt.BanditConvex

