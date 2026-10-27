import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model

namespace FakeUserRanking.FORC

/-- Lemma 1 (Decomposing Regret), p. 20. -/
theorem lemma_1 {n L : ℕ} (T F : ℕ) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P) :
    regret inst P A T ≤ (F : ℝ) + ∑ t : Fin T, ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
      gap inst j i * prob inst P A T (fun τ => feedbackEvent A τ t j i) := by sorry

end FakeUserRanking.FORC

