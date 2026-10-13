import Mathlib
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- A private value is an actual value, rather than the NIL marker. -/
def IsAuthScenario {α V : Type*} (P : Finset α) (σ : List α → Option V) : Prop :=
  ∀ p ∈ P, σ [p] ≠ none

/-- The messages visible to receiver `p`, with the receiver's leading letter removed. -/
def view {α V : Type*} (σ : List α → Option V) (p : α) : List α → Option V :=
  fun w => σ (p :: w)

/-- Section 5's two authentication conditions, restricted to the strings in an
`(m + 1)`-level scenario. Such strings have length at most `m + 2`. -/
def AuthConsistent {α V : Type*} (P N : Finset α) (m : ℕ)
    (σ : List α → Option V) : Prop :=
  (∀ p ∈ N, ∀ q ∈ P, ∀ w : List α,
    (∀ x ∈ w, x ∈ P) → (q :: p :: w).length ≤ m + 2 →
      σ (q :: p :: w) = σ (p :: w)) ∧
  (∀ p ∈ N, ∀ w' w : List α,
    (∀ x ∈ w', x ∈ P) → (∀ x ∈ w, x ∈ P) →
      (w' ++ p :: w).length ≤ m + 2 →
        σ (w' ++ p :: w) = σ (p :: w) ∨
        σ (w' ++ p :: w) = none)

end InteractiveConsistency.Authenticated
