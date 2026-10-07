import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Lemma 3.11 (p.68): if `θ̲_B < θ̄_S` and `θ̄_B > θ̲_S`, the ex ante expected difference
`E[t_B − t_S]` between the buyer's and the seller's transfers under the pivot mechanism is
negative. -/
theorem pivot_deficit (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) (hB : E.loB < E.hiS) (hS : E.loS < E.hiB) :
    (pivot E q hq).expectedSurplus < 0 := by sorry

end MechanismDesign.BilateralTrade

