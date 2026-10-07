import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.2, printed p. 52: w is the smallest TMD-superharmonic vector. -/
theorem value_smallest_superharmonic {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hfin : ∀ i, BddAbove (transientValues m i)) :
    IsSuperharmonic m (optimalValue m) ∧
    ∀ u : Fin n → ℝ, IsSuperharmonic m u → ∀ i, optimalValue m i ≤ u i := by sorry

end KallenbergLP.OptTransient

