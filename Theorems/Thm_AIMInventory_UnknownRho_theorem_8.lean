import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.UnknownRho

/-- Theorem 8, p. 13: the non-perishable AIM excess-cost bound for any
positive step scale `γ`. The right side is in `ℝ≥0∞`, so an infinite
hitting-time or busy-period expectation makes the bound infinite rather than
junk. `0 < ρ′` is added (the printed bound divides by `ρ′`). -/
theorem theorem_8 (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hNV : LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law c.h c.b ≤
      Real.toNNReal c.barY)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    (hmean : ρ' < CappedBaseStock.mean P) :
    ENNReal.ofReal (lambdaTwo P c T) ≤
      ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) *
        ((Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ')) +
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by sorry

end AIMInventory.UnknownRho

