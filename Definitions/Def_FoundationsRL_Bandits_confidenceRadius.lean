import Mathlib

namespace FoundationsRL.Bandits

/-- The UCB confidence radius of Foster–Rakhlin Eq. (2.19), p. 28: for `n` samples,
`sqrt(2 log(2T²A/δ) / n)`. The book's radius is `+∞` at `n = 0` (an arm never yet
sampled), so `n = 0` is deliberately left as junk here (division by `0` in the real
numbers, never used at `n = 0` by any caller): the book's UCB rule instead samples
every unsampled arm before ever comparing indices (see `ucb_regret_bound`'s first
optimism clause), so this function is only ever evaluated at `n > 0`. -/
noncomputable def confidenceRadius (T A : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (2 * (T : ℝ) ^ 2 * (A : ℝ) / δ) / n)

end FoundationsRL.Bandits
