import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.UnknownRho

/-- The displayed `E[K̃]` inequality in the proof of Theorem 8, p. 14.
Expectations retain `∞` on paths with no return. -/
theorem restart_bound (P : DemandLaw) (c : Parameters) (ρ' : ℝ)
    (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    (∫⁻ d, restartTime c ρ' d ∂CappedBaseStock.demandPathLaw P) ≤
      (Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ') := by sorry

end AIMInventory.UnknownRho

