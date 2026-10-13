import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem monopoly_quality_below_competitive {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    (∀ θ ∈ Set.Ico θlo θhi, deriv C 0 < θ → deriv C (q θ) < θ) ∧
    (∀ θ ∈ Set.Ico θlo θhi, θ ≤ deriv C 0 → q θ = 0) ∧
    ((deriv C 0 < θhi → ∃ L : ℝ, Tendsto q (𝓝[<] θhi) (𝓝 L) ∧ deriv C L = θhi) ∧
      (θhi ≤ deriv C 0 → Tendsto q (𝓝[<] θhi) (𝓝 0))) := by sorry

end MussaRosen.Mono

