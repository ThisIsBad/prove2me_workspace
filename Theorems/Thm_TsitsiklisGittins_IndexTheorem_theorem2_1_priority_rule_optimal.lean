import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_SemiMarkovBandit

namespace TsitsiklisGittins.IndexTheorem

/-- Theorem 2.1 of Tsitsiklis (1994), p. 196: if each `𝒳ᵢ` is finite, there exists a priority
rule which is optimal. -/
theorem theorem2_1_priority_rule_optimal {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X) :
    ∃ π : Policy n X, IsPriorityRule π ∧ B.IsOptimal π := by sorry

end TsitsiklisGittins.IndexTheorem

