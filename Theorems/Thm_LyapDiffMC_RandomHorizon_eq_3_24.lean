import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- (3.24), p. 13. The Lyapunov bound (3.12) together with Proposition 3.1 gives
`∫_C G(x, dy)(∫_C ω_ε(y, z) v₀(z) K(y, dz) + ∫_{Cᶜ} ω̃_ε(y, z)|f(z)| K(y, dz)) < ∞` for `x ∈ C`. -/
theorem eq_3_24 {S : Type*} [MeasurableSpace S] (M : Setting S)
    (θ₀ ε : ℝ) (hε : 0 < ε) (k : ℝ → S → S → ℝ)
    (hk_meas : ∀ θ ∈ Set.Icc (θ₀ - ε) (θ₀ + ε), Measurable (Function.uncurry (k θ)))
    (hA2 : ∀ x ∈ M.C, ∀ y, ContDiffOn ℝ 1 (fun θ => k θ x y) (Set.Icc (θ₀ - ε) (θ₀ + ε)))
    (v₀ v₁ : S → ℝ) (hv₀ : Measurable v₀) (hv₁ : Measurable v₁)
    (hv₀_nn : ∀ x ∈ M.C, 0 ≤ v₀ x) (hv₁_nn : ∀ x ∈ M.C, 0 ≤ v₁ x)
    (h312 : ∀ x ∈ M.C,
      ∫⁻ y in M.C, ENNReal.ofReal (v₁ y) ∂(discKernel M θ₀ x)
        + ∫⁻ y in M.C, omega k θ₀ ε x y * ENNReal.ofReal (v₀ y) ∂(discKernel M θ₀ x)
        + rtilde M k θ₀ ε x ≤ ENNReal.ofReal (v₁ x)) :
    ∀ x ∈ M.C,
      ∫⁻ y, (∫⁻ z in M.C, omega k θ₀ ε y z * ENNReal.ofReal (v₀ z) ∂(discKernel M θ₀ y)
          + ∫⁻ z in M.Cᶜ, omega k θ₀ ε y z * ‖M.f z‖ₑ ∂(discKernel M θ₀ y))
        ∂(greenMeasure M θ₀ x) < ⊤ := by sorry

end LyapDiffMC.RandomHorizon

