import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- Section 5, p. 233: a nonfaulty originator's value is the sole non-NIL
value visible in the receiver's set. -/
theorem nonfaulty_origin_set {α V : Type*} [DecidableEq α]
    (P N : Finset α) (m : ℕ) (σ : List α → Option V)
    (hmn : m ≤ P.card) (hN : N ⊆ P) (hcount : P.card ≤ N.card + m)
    (hscenario : IsAuthScenario P σ)
    (hconsistent : AuthConsistent P N m σ)
    (p q : α) (hp : p ∈ N) (hq : q ∈ N) :
    ∃ v : V, σ [q] = some v ∧ S m P (view σ p) p q = {v} := by sorry

end InteractiveConsistency.Authenticated

