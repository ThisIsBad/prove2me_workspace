import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Proof of Theorem 2.2 of Tsitsiklis (1994), p. 198: given the indices `γ` of a run of the index
algorithm, a state `x` can be picked before a state `y` by the index algorithm (in some run that
yields the same indices `γ`) if and only if `γ(x) ≥ γ(y)`. -/
theorem picked_before_iff_index_ge {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (x y : Σ i, X i) (hxy : x ≠ y) :
    γ y ≤ γ x ↔ ∃ seq' : List (Σ i, X i), B.IsIndexRun seq' γ ∧ seq'.idxOf x < seq'.idxOf y := by sorry

end TsitsiklisGittins.IndexTheorem

