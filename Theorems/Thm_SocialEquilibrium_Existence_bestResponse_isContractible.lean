import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §2, p. 889 (proof of the THEOREM, first paragraph): if every best-response
set `M_{ā_ι}` is contractible, then `φ(a) = M_{ā_1} × ⋯ × M_{ā_ν}` is contractible for every
profile `a ∈ 𝔄`. -/
theorem bestResponse_isContractible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal)
    (hM : ∀ i (ā : Others X i), IsContractible (bestSet X A f i ā)) :
    ∀ a : ∀ j, X j, IsContractible (bestResponse X A f a) := by sorry

end SocialEquilibrium.Existence
