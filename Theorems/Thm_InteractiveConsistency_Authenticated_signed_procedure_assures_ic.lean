import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- Section 5, pp. 233–234: the authenticated-message procedure assures
interactive consistency for every `n ≥ m`. -/
theorem signed_procedure_assures_ic {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hmn : m ≤ P.card) :
    ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m →
    ∀ σ : List α → Option V,
      IsAuthScenario P σ → AuthConsistent P N m σ →
      (∀ p ∈ N, ∀ q ∈ N, record m P (view σ p) p q = σ [q]) ∧
      (∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        record m P (view σ p) p r = record m P (view σ p') p' r) := by sorry

end InteractiveConsistency.Authenticated

