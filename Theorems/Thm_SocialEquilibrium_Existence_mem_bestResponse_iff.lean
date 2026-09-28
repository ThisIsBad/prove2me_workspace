import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, last paragraph): a profile `a*` is a fixed
point of `φ(a) = M_{ā_1} × ⋯ × M_{ā_ν}`, i.e. `a*_ι ∈ M_{ā*_ι}` for all `ι`, exactly when `a*` is
an equilibrium point. -/
theorem mem_bestResponse_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) :
    a ∈ bestResponse X A f a ↔ IsEquilibrium X A f a := by sorry

end SocialEquilibrium.Existence
