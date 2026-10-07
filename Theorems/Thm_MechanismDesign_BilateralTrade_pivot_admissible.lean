import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Lemma 3.9 (p.67): the pivot mechanism (Definition 3.10) is incentive-compatible and
individually rational. Stated for every measurable first-best trading rule `q*` (any tie rule);
the conclusion also records that the pivot mechanism is well defined (measurable, integrable). -/
theorem pivot_admissible (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) :
    (pivot E q hq).Admissible := by sorry

end MechanismDesign.BilateralTrade

