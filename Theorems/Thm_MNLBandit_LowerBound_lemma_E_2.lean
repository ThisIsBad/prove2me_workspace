import Mathlib
import Definitions.Def_MNLBandit_LowerBound_BernoulliMAB

namespace MNLBandit.LowerBound

theorem lemma_E_2 (N : ℕ) (hN : 12 ≤ N) (α ϵ : ℝ) (hα : 0 < α) (hϵ : 0 < ϵ)
    (hϵ4 : ϵ ≤ 1 / 4) (hαϵ : 2 * α + ϵ ≤ 1)
    (A : MABAlg N) (hA : IsMABAlg A) (s : ℕ)
    (hs : (s : ℝ) + 1 ≤ (N : ℝ) * α / (60 * ϵ ^ 2)) :
    ∃ J : Finset (Fin N), (N : ℝ) / 3 ≤ J.card ∧
      ∀ j ∈ J, armProb A (imabMeans α ϵ j) s j ≤ 1 / 2 := by sorry

end MNLBandit.LowerBound

