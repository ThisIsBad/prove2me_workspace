import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal

namespace SennottDP.MarkovCost

variable {S : Type} [Countable S]

open Classical in
/-- Sennott (1999), p. 298: `c_{iG}`, the expected cost of a first passage from `i` to `G`,
`E[∑_{t=0}^{T_{iG}-1} C(X_t) | X_0 = i]`, where each state `k` carries a finite nonnegative cost
`C(k)`. It is computed over the first passage paths `x_0 = i, x_1, …, x_t` (`t ≥ 1`,
`x_1, …, x_{t-1} ∉ G`, `x_t ∈ G`), each weighted by its probability and charged
`C(x_0) + ⋯ + C(x_{t-1})`. The book defines `c_{iG}` only when `m_{iG} < ∞` (then
`T_{iG} < ∞` with probability one and this is the expectation); every result of this development
uses `passageCost` only under that proviso. -/
noncomputable def passageCost (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' x : Fin (t + 1) → S,
    if t ≠ 0 ∧ x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G) ∧
        x (Fin.last t) ∈ G
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

/-- Sennott (1999), (C.11), p. 298: `J^{(n)}_i = (1/n) E[∑_{t=0}^{n-1} C(X_t) | X_0 = i]
= ∑_j C(j) Q^{(n)}_{ij}`, the expected cost per unit time in `[0, n − 1]` from `i`, in `[0, ∞]`
(meaningful for `n ≥ 1`). -/
noncomputable def avgCostN (M : MC S) (C : S → ℝ≥0) (n : ℕ) (i : S) : ℝ≥0∞ :=
  (∑ t ∈ Finset.range n, ∑' j, nStep M t i j * (C j : ℝ≥0∞)) / (n : ℝ≥0∞)

/-- Sennott (1999), Proposition C.2.1(i), p. 298: the average cost on a positive recurrent class
`R`, `J_R = ∑_{j ∈ R} π_j C(j)`, a finite or infinite constant. -/
noncomputable def classAvgCost (M : MC S) (C : S → ℝ≥0) (R : Set S) : ℝ≥0∞ :=
  ∑' j : R, steadyState M j * (C j : ℝ≥0∞)

/-- Sennott (1999), Definition C.2.5, p. 301: the Markov chain with costs is `z` standard if
`m_{iz} < ∞` and `c_{iz} < ∞` for all `i ∈ S` (including `i = z`: the expected return time to `z`
and the expected cost of a return to `z` are finite). -/
def IsZStandard (M : MC S) (C : S → ℝ≥0) (z : S) : Prop :=
  ∀ i, meanPassage M {z} i < ⊤ ∧ passageCost M C {z} i < ⊤

end SennottDP.MarkovCost
