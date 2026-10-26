import Mathlib
import Definitions.Def_MNLBandit_LowerBound_BernoulliMAB

namespace MNLBandit.LowerBound

theorem lemma_5_1 (N : ℕ) (hN : 2 ≤ N) (α : ℝ) (hα : 0 < α) (T : ℕ) (hT : 1 ≤ T)
    (hαϵ : 2 * α + epsMAB N α T ≤ 1) (A : MABAlg N) (hA : IsMABAlg A) :
    epsMAB N α T * T / 6 ≤ regretIMAB A α (epsMAB N α T) T := by sorry

end MNLBandit.LowerBound

