import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.3, p. 300. Let `G` be a nonempty subset of `S` with
`m_{iG} < ∞` for all `i ∉ G`. Let `r` be a finite nonnegative function on `S` and `H ⊆ S − G` a
finite set with (C.14): `∑_j P_{ij}[r(j) − r(i)] ≤ −C(i)` for `i ∉ G ∪ H` (written
`∑_j P_{ij} r(j) + C(i) ≤ r(i)`) and `∑_j P_{ij} r(j) < ∞` for `i ∈ H`. Then there is a finite
nonnegative constant `F` with `c_{iG} ≤ r(i) + F m_{iG}` for `i ∉ G`; if `H = ∅`, then
`c_{iG} ≤ r(i)` for `i ∉ G`. -/
theorem lyapunov_passage_cost_bound {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0)
    (G : Set S) (hG : G.Nonempty) (hm : ∀ i ∉ G, meanPassage M G i < ⊤)
    (r : S → ℝ≥0) (H : Finset S) (hHG : Disjoint (H : Set S) G)
    (hdrift : ∀ i ∉ G, i ∉ H → ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i)
    (hH : ∀ i ∈ H, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤) :
    (∃ F : ℝ≥0, ∀ i ∉ G, passageCost M C G i ≤ r i + F * meanPassage M G i) ∧
    (H = ∅ → ∀ i ∉ G, passageCost M C G i ≤ r i) := by sorry

end SennottDP.MarkovCost
