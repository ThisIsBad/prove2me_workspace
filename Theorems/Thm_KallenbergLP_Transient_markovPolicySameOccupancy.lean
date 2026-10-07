import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Corollary 2.5.1: for a fixed initial state, a memoryless policy reproduces every
state-action probability of an arbitrary policy. -/
theorem markovPolicySameOccupancy
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (i : Fin N) (R : Policy M) :
    ∃ R₀ : Policy M, Memoryless M R₀ ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        occupancy M R₀ i j a t = occupancy M R i j a t := by sorry

end KallenbergLP.Transient

