import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace AIMInventory.UnknownRho

/-- Claim (14), p. 14, with the random lower summation limit inside the
expectation, as required by (13) and Appendix E. -/
theorem claim_14 (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    (hmean : ρ' < CappedBaseStock.mean P) :
    ENNReal.ofReal (c.h / (T : ℝ)) *
      (∫⁻ d, ∑ t ∈ Finset.Icc 1 T,
        if restartTime c ρ' d < (t : ℝ≥0∞) then
          ENNReal.ofReal (Z d (m c) t) else 0
        ∂CappedBaseStock.demandPathLaw P) ≤
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by sorry

end AIMInventory.UnknownRho

