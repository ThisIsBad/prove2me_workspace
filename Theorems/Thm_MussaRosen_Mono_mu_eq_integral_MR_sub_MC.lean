import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem mu_eq_integral_MR_sub_MC {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) :
    ∀ t ∈ Set.Icc θlo θhi,
      mu D C q t = ∫ θ in t..θhi, (virtualValuation D θ - deriv C (q θ)) * D.f θ := by sorry

end MussaRosen.Mono

