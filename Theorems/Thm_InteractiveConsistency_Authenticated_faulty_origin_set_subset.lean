import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- Section 5, p. 234: for a faulty originator, every non-NIL report seen by
one nonfaulty receiver is also seen by every other nonfaulty receiver. -/
theorem faulty_origin_set_subset {α V : Type*} [DecidableEq α]
    (P N : Finset α) (m : ℕ) (σ : List α → Option V)
    (hmn : m ≤ P.card) (hN : N ⊆ P) (hcount : P.card ≤ N.card + m)
    (hscenario : IsAuthScenario P σ)
    (hconsistent : AuthConsistent P N m σ)
    (p p' q : α) (hp : p ∈ N) (hp' : p' ∈ N)
    (hqP : q ∈ P) (hqN : q ∉ N) :
    S m P (view σ p) p q ⊆ S m P (view σ p') p' q := by sorry

end InteractiveConsistency.Authenticated

