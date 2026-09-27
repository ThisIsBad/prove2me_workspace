import Mathlib

namespace OnlineConvexOpt.Introduction

variable {N : ℕ}

/-- One run of the Randomized Weighted Majority algorithm (RWM, §1.3.2, p. 11) with `N`
experts and decay parameter `ε`, against adversarially chosen expert predictions
`expertPredict` and true outcomes `outcome`. `W` are the same weights as Weighted Majority
(`W 0 i = 1`, correct experts keep their weight, mistaken experts are scaled by `(1 - ε)`);
`p` is the probability RWM assigns to each expert at each round,
`p_t(i) = W_t(i) / ∑_j W_t(j)`. -/
structure IsRandomizedWeightedMajorityRun (ε : ℝ) (expertPredict : ℕ → Fin N → Bool)
    (outcome : ℕ → Bool) (W : ℕ → Fin N → ℝ) (p : ℕ → Fin N → ℝ) : Prop where
  weight_init : ∀ i, W 0 i = 1
  weight_update : ∀ t i, W (t + 1) i =
    if expertPredict t i = outcome t then W t i else W t i * (1 - ε)
  prob_def : ∀ t i, p t i = W t i / ∑ j, W t j

/-- Expected number of mistakes RWM makes over rounds `0, …, T - 1`, `E[M_T]` in the book's
notation: at each round the algorithm errs with probability equal to the total probability
mass on mistaken experts, `∑_i p_t(i) · 1[\text{expert } i \text{ erred at } t]`. -/
noncomputable def expectedMistakes {N : ℕ} (expertPredict : ℕ → Fin N → Bool)
    (outcome : ℕ → Bool) (p : ℕ → Fin N → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i, p t i * (if expertPredict t i ≠ outcome t then (1 : ℝ) else 0)

end OnlineConvexOpt.Introduction
