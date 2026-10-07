import Definitions.Def_KallenbergLP_Transient_Criteria
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 2.5.1: a memoryless policy reproduces a mixture's one-period occupancies. -/
theorem dermanStrauch
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1)
    (R : ℕ → Policy M) (w : ℕ → ℝ)
    (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : HasSum w 1) :
    ∃ Q : Policy M, Memoryless M Q ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        (∑ i : Fin N, β i * occupancy M Q i j a t) =
          ∑' k : ℕ, w k *
            (∑ i : Fin N, β i * occupancy M (R k) i j a t) := by sorry

end KallenbergLP.Transient

