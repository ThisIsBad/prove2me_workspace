import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 80, Corollary 5.7.1: let D and D.2 hold, let `S` be a finite set,
and let `J*(x) > −∞` for all `x ∈ S`. Then for every `ε > 0` there is a policy `π_ε` with
`J* ≤ J_{π_ε} ≤ J* + ε`. -/
theorem cor5_7_1_finite_state_eps_optimal {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
      m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal) := by sorry

end BertsekasShreve.Monotone

