import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem rp_to_artificial (P : RPParams) (hP : P.Standing) (q : ℝ → ℝ)
    (S θ SQ θQ : ℝ → ℝ → ℝ)
    (h24a : ∀ y η : ℝ, SQ (toYQ P y) (toMuQ P η) = Real.exp (shift P) * S y η)
    (h24b : ∀ y η : ℝ, θQ (toYQ P y) (toMuQ P η) = θ y η)
    (h19 : IsEquilibriumRP P q S θ) :
    IsEquilibriumNoRP (artificial P) q SQ θQ := by sorry

end RiskPremiaDMP.Equivalence

