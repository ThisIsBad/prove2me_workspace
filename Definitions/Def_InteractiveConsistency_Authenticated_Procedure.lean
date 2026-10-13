import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Scenario
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- The non-NIL values obtained for `q` from paths with distinct intermediate
processors, excluding the receiver `p` and the originator `q`. -/
def S {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ : List α → Option V) (p q : α) : Set V :=
  {v | ∃ w : List α, w.Nodup ∧ w.length ≤ m ∧
    (∀ x ∈ w, x ∈ P ∧ x ≠ p ∧ x ≠ q) ∧ τ (w ++ [q]) = some v}

/-- Record the unique non-NIL value when there is one, and NIL otherwise. -/
noncomputable def record {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ : List α → Option V) (p q : α) : Option V := by
  classical
  exact if h : ∃ v : V, S m P τ p q = {v} then some h.choose else none

end InteractiveConsistency.Authenticated
