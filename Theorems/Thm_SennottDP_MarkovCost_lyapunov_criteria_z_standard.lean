import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Remark C.2.7, pp. 301–302.
(i) If the hypotheses of Corollaries C.1.6 and C.2.4 hold (a Lyapunov function `y` with `ε > 0`,
`∑_j P_{zj} y(j) < ∞` and (C.10), and a finite nonnegative `r` with a finite set `H* ∋ z` satisfying
(C.16)), then `Γ` is `z` standard.
(ii) If `Γ` is irreducible and positive recurrent with finite average cost, then it is `z` standard
for any state `z`. -/
theorem lyapunov_criteria_z_standard {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) :
    (∀ (z : S) (y : S → ℝ≥0) (ε : ℝ≥0), 0 < ε → ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤ →
      (∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) →
      ∀ (r : S → ℝ≥0) (Hs : Finset S), z ∈ Hs →
      (∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤) →
      (∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) →
      IsZStandard M C z) ∧
    (Irreducible M → (∀ i, PositiveRecurrent M i) → classAvgCost M C Set.univ < ⊤ →
      ∀ z, IsZStandard M C z) := by sorry

end SennottDP.MarkovCost

