import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Asymp_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Asymp

theorem sampling_error_bound
    {n m N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) (hΓ : You2015.Shared.IsGenerator Γ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ K₃ : ℝ) (h21 : Assumption21 f g K₁ K₂) (h22 : Assumption22 u K₃)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r₀ : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : You2015.Shared.HybridSetup P m N Γ r₀) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hx : You2015.Shared.SolvesSampledHybridSDE S f u g τ x₀ x) :
    ∀ t : ℝ≥0, ∫⁻ ω, ‖x t ω - x (You2015.Shared.delta τ t) ω‖ₑ ^ 2 ∂P ≤
      2 * ∫⁻ ω, ∫⁻ s in Set.Icc (You2015.Shared.delta τ t : ℝ) t,
        ((τ : ℝ≥0∞) * ‖(f (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal + u (x (You2015.Shared.delta τ s.toNNReal) ω) (S.r s.toNNReal ω) s.toNNReal)‖ₑ ^ 2
          + ∑ k, ‖(g (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal k)‖ₑ ^ 2) ∂volume ∂P := by sorry

end You2015.Asymp
