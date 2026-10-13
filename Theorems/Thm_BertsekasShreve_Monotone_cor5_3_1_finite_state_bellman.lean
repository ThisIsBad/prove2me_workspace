import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 76, Corollary 5.3.1: let D and D.2 hold, let `S` be a finite set,
and let `J*(x) > −∞` for all `x ∈ S`. Then `J* = T(J*)`; furthermore every `J' ∈ F` with
`J' ≤ J₀` and `J' ≤ T(J')` satisfies `J' ≤ J*`. -/
theorem cor5_3_1_finite_state_bellman {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.T J' → J' ≤ m.Jstar := by sorry

end BertsekasShreve.Monotone

