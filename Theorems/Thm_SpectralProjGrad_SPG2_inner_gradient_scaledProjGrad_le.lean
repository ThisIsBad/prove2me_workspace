import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad

namespace SpectralProjGrad.SPG2

/-- Lemma 2.1 (i): for `x ∈ Ω` and `t ∈ (0, α_max]`,
`⟨g(x), g_t(x)⟩ ≤ -(1/t) ‖g_t(x)‖₂² ≤ -(1/α_max) ‖g_t(x)‖₂²`. -/
theorem inner_gradient_scaledProjGrad_le {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {αmin αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) ≤ -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ∧
      -(1 / t) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 ≤ -(1 / αmax) * ‖SpectralProjGrad.Shared.scaledProjGrad P f t x‖ ^ 2 := by sorry

end SpectralProjGrad.SPG2

