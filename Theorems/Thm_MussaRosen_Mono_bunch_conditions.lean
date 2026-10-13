import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem bunch_conditions {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    (θu θv qr : ℝ) (hlo : θlo < θu) (huv : θu < θv) (hhi : θv < θhi) (hqr : 0 < qr)
    (hflat : ∀ θ ∈ Set.Icc θu θv, q θ = qr)
    (hleft : ∃ a : ℝ, θlo ≤ a ∧ a < θu ∧
      ∀ θ ∈ Set.Ioo a θu, ∃ d : ℝ, 0 < d ∧ HasDerivAt q d θ)
    (hright : ∃ b : ℝ, θv < b ∧ b ≤ θhi ∧
      ∀ θ ∈ Set.Ioo θv b, ∃ d : ℝ, 0 < d ∧ HasDerivAt q d θ) :
    deriv C qr = virtualValuation D θu ∧ deriv C qr = virtualValuation D θv ∧
      ∫ θ in θu..θv, (virtualValuation D θ - deriv C qr) * D.f θ = 0 := by sorry

end MussaRosen.Mono

