import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem proposition_1 (P : RPParams) (hP : P.Standing) (q : ℝ → ℝ) :
    (artificial P).Standing ∧
    (∀ S θ SQ θQ : ℝ → ℝ → ℝ,
      (∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η) →
      (∀ y η : ℝ, θQ (toYQ P y) (toMuQ P η) = θ y η) →
      (IsEquilibriumRP P q S θ ↔ IsEquilibriumNoRP (artificial P) q SQ θQ)) ∧
    (∀ y η BP Bη : ℝ → ℝ, Continuous y → Continuous η →
      SolvesPhysicalY P y BP → SolvesMPR P η Bη →
      SolvesProductivity (artificial P) (fun t => toYQ P (y t)) (fun t => toMuQ P (η t))
        (riskNeutralBM η BP) (fun t => -Bη t)) := by sorry

end RiskPremiaDMP.Equivalence

