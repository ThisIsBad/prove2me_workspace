import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts
import Definitions.Def_OnlineConvexOpt_Introduction_WeightedMajority

namespace OnlineConvexOpt.Introduction

/-- **Lemma 1.3** (Weighted Majority mistake bound), Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 9.

"Denote by `M_T` the number of mistakes the algorithm makes until time `T`, and by `M_T(i)`
the number of mistakes made by expert `i` until time `T`. Then, for any expert `i ∈ [N]` we
have `M_T ≤ 2(1 + ε) M_T(i) + 2 log N / ε`."

`0 < ε < 1/2` is the range under which the book's own proof of this lemma (via the bound
`-x - x² ≤ log(1 - x) ≤ -x` for `0 < x < 1/2`) is valid; the same range is stated explicitly
for Theorem 1.2, the corollary that packages this lemma together with Lemma 1.4. -/
theorem weighted_majority_mistake_bound {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (expertPredict : ℕ → Fin N → Bool) (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ)
    (algPredict : ℕ → Bool) (hrun : IsWeightedMajorityRun ε expertPredict outcome W algPredict)
    (T : ℕ) (i : Fin N) :
    (algMistakes algPredict outcome T : ℝ) ≤
      2 * (1 + ε) * (expertMistakes expertPredict outcome i T : ℝ) + 2 * Real.log N / ε := by sorry

end OnlineConvexOpt.Introduction
