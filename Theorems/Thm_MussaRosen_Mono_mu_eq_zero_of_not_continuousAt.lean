import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem mu_eq_zero_of_not_continuousAt {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ θ ∈ Set.Ioo θlo θhi, ¬ ContinuousAt q θ → mu D C q θ = 0 := by sorry

end MussaRosen.Mono

