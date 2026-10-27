import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

namespace RiskPremiaDMP.Equivalence

theorem risk_neutral_productivity (P : RPParams) (hP : P.Standing) (y η BP : ℝ → ℝ)
    (hy : Continuous y) (hη : Continuous η) (h9 : SolvesPhysicalY P y BP) :
    SolvesRiskNeutralY P y η (riskNeutralBM η BP) := by sorry

end RiskPremiaDMP.Equivalence

