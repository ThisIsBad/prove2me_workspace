import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Theorem 2.2 of Tsitsiklis (1994), p. 198: let the index `γ` of each state be determined by
(any run of) the index algorithm. Then any priority policy in which states with a higher index
have higher priority is optimal. -/
theorem theorem2_2_index_priority_optimal {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (rank : (Σ i, X i) → ℕ) (hinj : Function.Injective rank)
    (hcompat : ∀ x y : Σ i, X i, γ y < γ x → rank y < rank x)
    (π : Policy n X) (hπ : FollowsRank rank π) :
    B.IsOptimal π := by sorry

end TsitsiklisGittins.IndexTheorem

