import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal

namespace SennottDP.SEN

/-- Sennott (1999), Lemma 7.2.1, p. 133: let `e` be a stationary policy. Assume there exist a
(finite) constant `J` and a (finite) function `h` that is bounded below in `i` such that
`J + h(i) ≥ C(i,e) + ∑_j P_{ij}(e) h(j)` for `i ∈ S` (7.4). Then `J_e(i) ≤ J` for `i ∈ S`.
The sum `∑_j P_{ij}(e) h(j)` is `wsum` (well defined in `(−∞, ∞]` since `h` is bounded below);
the comparison `J_e(i) ≤ J` is made in `EReal`, since `J_e(i) ∈ [0, ∞]` and `J ∈ ℝ`. -/
theorem lemma_7_2_1_acoi_bound {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (e : StationaryPolicy M) (J : ℝ) (h : S → ℝ) (hbdd : BddBelow (Set.range h))
    (h74 : ∀ i, ((M.C i (e.1 i) : ℝ) : EReal) + wsum (M.P i (e.1 i)) h ≤ ((J + h i : ℝ) : EReal)) :
    ∀ i, (avgCost M e.toPolicy i : EReal) ≤ (J : EReal) := by sorry

end SennottDP.SEN

