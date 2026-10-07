import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Lemma 3.10 (p.67): the ex ante expected difference `E[t_B − t_S]` between the buyer's and the
seller's transfers under the pivot mechanism is at least as large as under any well-defined,
incentive-compatible and individually rational direct mechanism `m` that implements a first-best
trading rule. -/
theorem pivot_maximizes_surplus (E : Environment) (q : ℝ × ℝ → ℝ) (hq : IsFirstBestRule E q)
    (hqm : Measurable q) (m : DirectMechanism E) (hm : m.Admissible)
    (hfb : IsFirstBestRule E m.q) :
    m.expectedSurplus ≤ (pivot E q hq).expectedSurplus := by sorry

end MechanismDesign.BilateralTrade

