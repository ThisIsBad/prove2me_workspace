import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_SemiMarkovBandit

namespace TsitsiklisGittins.IndexTheorem

/-- Lemma 2.1 of Tsitsiklis (1994), p. 196: if `s = ⟨i*, s*⟩` has maximal reward rate (2.1),
`r(s*) = max_{x ∈ 𝒳} r(x)`, then there exists an optimal policy that plays bandit `i*` whenever
bandit `i*` is at state `s*`. -/
theorem lemma2_1_top_priority {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (s : Σ i, X i) (hmax : ∀ q : Σ i, X i, B.rate q ≤ B.rate s) :
    ∃ π : Policy n X, B.IsOptimal π ∧ ∀ z : JointState n X, z s.1 = s.2 → π z = s.1 := by sorry

end TsitsiklisGittins.IndexTheorem

