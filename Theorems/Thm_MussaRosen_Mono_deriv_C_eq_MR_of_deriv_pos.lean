import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem deriv_C_eq_MR_of_deriv_pos {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    (a b : ℝ) (ha : θlo ≤ a) (hab : a < b) (hb : b ≤ θhi)
    (hinc : ∀ θ ∈ Set.Ioo a b, ∃ d : ℝ, 0 < d ∧ HasDerivAt q d θ) :
    ∀ θ ∈ Set.Ioo a b, deriv C (q θ) = virtualValuation D θ := by sorry

end MussaRosen.Mono

