import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts
import Definitions.Def_OnlineConvexOpt_Introduction_RandomizedWeightedMajority

namespace OnlineConvexOpt.Introduction

/-- **Lemma 1.4** (Randomized Weighted Majority mistake bound), Hazan, *Introduction to
Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 11.

"Let `M_T` denote the number of mistakes made by RWM until iteration `T`. Then, for any
expert `i ∈ [N]` we have `E[M_T] ≤ (1 + ε) M_T(i) + log N / ε`."

As in Lemma 1.3, `0 < ε < 1/2` is the range under which the book's own proof (the same
logarithm bound, `-x - x² ≤ log(1 - x) ≤ -x` for `0 < x < 1/2`) is valid, matching Theorem
1.2's explicit range for the corollary that packages this lemma. -/
theorem randomized_weighted_majority_mistake_bound {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W p : ℕ → Fin N → ℝ)
    (hrun : IsRandomizedWeightedMajorityRun ε expertPredict outcome W p)
    (T : ℕ) (i : Fin N) :
    expectedMistakes expertPredict outcome p T ≤
      (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + Real.log N / ε := by sorry

end OnlineConvexOpt.Introduction
