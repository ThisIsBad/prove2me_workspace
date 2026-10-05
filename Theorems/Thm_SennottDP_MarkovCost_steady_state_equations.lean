import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.1.2, p. 295. Let `R` be a positive recurrent class.
(i) `π_j = ∑_{i ∈ R} P_{ij} π_i` for `j ∈ R` and `∑_{j ∈ R} π_j = 1`, and every nonnegative solution
of these equations equals `π` on `R`.
(ii) For `i, j ∈ R`, with `e_{ij} = _{\{i\}} u_{ij}` the expected number of visits to `j` during a
first passage from `i` to `i`, `π_j = e_{ij} / m_{ii} = π_i e_{ij}`. -/
theorem steady_state_equations {S : Type} [Countable S] (M : MC S) (R : Set S)
    (hR : IsPosRecClass M R) :
    ((∀ j ∈ R, steadyState M j = ∑' i : R, M.P i j * steadyState M i) ∧
      ∑' j : R, steadyState M j = 1 ∧
      ∀ x : S → ℝ≥0∞, (∀ j ∈ R, x j = ∑' i : R, M.P i j * x i) → ∑' j : R, x j = 1 →
        ∀ j ∈ R, x j = steadyState M j) ∧
    (∀ i ∈ R, ∀ j ∈ R,
      steadyState M j = visits M {i} i j / meanPassage M {i} i ∧
      steadyState M j = steadyState M i * visits M {i} i j) := by sorry

end SennottDP.MarkovCost

