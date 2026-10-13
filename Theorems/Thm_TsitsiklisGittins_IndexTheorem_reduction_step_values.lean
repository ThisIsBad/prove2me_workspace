import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_Reduction

namespace TsitsiklisGittins.IndexTheorem

/-- Reduction step in the proof of Theorem 2.1 of Tsitsiklis (1994), p. 197. Let `s = ⟨i*, s*⟩`
have maximal reward rate and let `𝒳_{i*}` not be a singleton. Reducing bandit `i*` by removing
`s*` gives a new multi-armed bandit problem (a valid stage) with one state fewer, and
(a) every policy giving top priority to `s*` has, from every joint state in which bandit `i*` is
not at `s*`, the same expected discounted reward in the original and in the reduced problem;
(b) every policy of the reduced problem has, on those joint states, the value of such a policy. -/
theorem reduction_step_values {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (s : Σ i, X i) (hmax : ∀ q : Σ i, X i, B.rate q ≤ B.rate s) (hns : ∃ x : X s.1, x ≠ s.2) :
    (B.initStage.reduce s).Valid B.β ∧
      (B.initStage.reduce s).alive.card + 1 = Fintype.card (Σ i, X i) ∧
      (∀ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) →
        ∀ z : JointState n X, z s.1 ≠ s.2 → B.value π z = (B.initStage.reduce s).value π z) ∧
      (∀ π' : Policy n X, ∃ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) ∧
        ∀ z : JointState n X, z s.1 ≠ s.2 →
          (B.initStage.reduce s).value π z = (B.initStage.reduce s).value π' z) := by sorry

end TsitsiklisGittins.IndexTheorem

