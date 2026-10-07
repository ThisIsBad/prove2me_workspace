import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.1, printed p. 50: a finite transient value satisfies the Bellman equation. -/
theorem bellman_value {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hfin : ∀ i, BddAbove (transientValues m i)) :
    ∀ i : Fin n, ∃ a : {a : α // a ∈ m.actions i},
      optimalValue m i = m.reward i a.1 + ∑ j, m.transition i a.1 j * optimalValue m j ∧
      ∀ b : {b : α // b ∈ m.actions i},
        m.reward i b.1 + ∑ j, m.transition i b.1 j * optimalValue m j ≤ optimalValue m i := by sorry

end KallenbergLP.OptTransient

