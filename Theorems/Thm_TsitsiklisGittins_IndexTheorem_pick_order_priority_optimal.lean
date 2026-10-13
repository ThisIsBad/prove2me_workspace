import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Proof of Theorem 2.2 of Tsitsiklis (1994), p. 198: any priority policy that orders the states
in the same order as they are picked by (a run of) the index algorithm is optimal. -/
theorem pick_order_priority_optimal {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (rank : (Σ i, X i) → ℕ)
    (hord : ∀ (a b : ℕ) (ha : a < seq.length) (hb : b < seq.length), a < b → rank seq[b] < rank seq[a])
    (π : Policy n X) (hπ : FollowsRank rank π) :
    B.IsOptimal π := by sorry

end TsitsiklisGittins.IndexTheorem

