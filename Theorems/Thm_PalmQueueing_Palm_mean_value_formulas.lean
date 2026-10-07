import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eqs. (1.3.2) and (1.3.3): the mean-value formulas (§1.3.1, p.21)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The mean-value formulas**, Eqs. (1.3.2) and (1.3.3) (§1.3.1, p.21). Let `{Z_t}` take values
in a measurable space `(K, 𝒦)` and satisfy `(1.3.1) Z_t = Z₀ ∘ θ_t`. Then for every non-negative
measurable `g : (K, 𝒦) → (ℝ, B)`, the stationary and Palm expectations of `g(Z₀)` each express the
other as a ratio:

`(1.3.2)  E[g(Z₀)] = E⁰_N[ ∫_0^{T₁} g(Z_t) dt ] / E⁰_N[T₁]`,

`(1.3.3)  E⁰_N[g(Z₀)] = E[ Σ_{n ∈ ℤ} g(Z_{T_n}) 1_{T_n ∈ (0,1]} ] / E[ Σ_{n ∈ ℤ} 1_{T_n ∈ (0,1]} ]`.

The book records that these "just rephrase the inversion formula (1.2.25) and the definition
formula (1.2.1) of `P⁰_N`", and that (1.3.2) is the familiar renewal- and regenerative-process
identity. Both denominators are non-zero and finite: `E⁰_N[T₁] = 1/λ` by (1.2.27) and the second is
`λ` itself. -/
theorem mean_value_formulas {K : Type*} [MeasurableSpace K] (S : PalmSetting Ω)
    (Z : ℝ → Ω → K) (hZmeas : ∀ t, Measurable (Z t))
    (hZ : ∀ (t : ℝ) (ω : Ω), Z t ω = Z 0 (S.θ t ω))
    (g : K → ENNReal) (hg : Measurable g) :
    (∫⁻ ω, g (Z 0 ω) ∂S.P
        = (∫⁻ ω, ∫⁻ t in Set.Ioc (0 : ℝ) (S.N.T 1 ω), g (Z t ω) ∂(volume : Measure ℝ) ∂S.P0)
            / (∫⁻ ω, ENNReal.ofReal (S.N.T 1 ω) ∂S.P0))
      ∧ (∫⁻ ω, g (Z 0 ω) ∂S.P0
        = (∫⁻ ω, ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => g (Z (S.N.T n ω) ω)) (S.N.T n ω) ∂S.P)
            / (∫⁻ ω, ∑' n : ℤ,
              Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ENNReal)) (S.N.T n ω) ∂S.P)) := by sorry

end PalmQueueing.Palm

