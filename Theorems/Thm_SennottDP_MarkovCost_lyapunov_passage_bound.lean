import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.1.5, pp. 296–297. Let `G` be a nonempty subset of `S`, `y` a
finite nonnegative function on `S` and `ε > 0` with (C.7) `∑_j P_{ij}[y(j) − y(i)] ≤ −ε` for
`i ∉ G`, written equivalently as `∑_j P_{ij} y(j) + ε ≤ y(i)` (the left side of (C.7) is `+∞` when
`∑_j P_{ij} y(j) = ∞`). Then for `i ∉ G`, `P(T_{iG} < ∞) = 1` and `m_{iG} ≤ y(i)/ε`. -/
theorem lyapunov_passage_bound {S : Type} [Countable S] (M : MC S) (G : Set S)
    (hG : G.Nonempty) (y : S → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (hdrift : ∀ i ∉ G, ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) :
    ∀ i ∉ G, hitProb M G i = 1 ∧ meanPassage M G i ≤ (y i : ℝ≥0∞) / ε := by sorry

end SennottDP.MarkovCost
