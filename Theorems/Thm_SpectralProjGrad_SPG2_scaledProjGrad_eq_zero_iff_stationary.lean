import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
import Definitions.Def_SpectralProjGrad_Shared_IsConstrainedStationary

namespace SpectralProjGrad.SPG2

/-- Lemma 2.1 (ii): for `x̄ ∈ Ω` and `t ∈ (0, α_max]`, the scaled projected gradient
`g_t(x̄) = P(x̄ - t ∇f(x̄)) - x̄` vanishes iff `x̄` is a constrained stationary point. -/
theorem scaledProjGrad_eq_zero_iff_stationary {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : xbar ∈ Ω) :
    SpectralProjGrad.Shared.scaledProjGrad P f t xbar = 0 ↔ SpectralProjGrad.Shared.IsConstrainedStationary Ω f xbar := by sorry

end SpectralProjGrad.SPG2

