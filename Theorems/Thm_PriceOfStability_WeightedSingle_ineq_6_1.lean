import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

open scoped ENNReal

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, proof, inequality (6.1), p. 1620 (PDF p. 19).

In the weighted single-commodity game with weights `wᵢ ≥ 1` and positive arc costs, suppose that
player `i` makes a best-response move from `S` to `S'`, switching from the path `P₁ = Sᵢ` to the
path `P₂ = S'ᵢ`. Let `𝒫` be the set of simple `s`–`t` paths that share an arc with `P₁ ∪ P₂`.
Then the minimum over `𝒫` of the marginal costs after the move is strictly smaller than the
minimum before it: `min_{P∈𝒫} c_{P₂}(P) < min_{P∈𝒫} c(P)`.

**Formalization Note.** Arc costs are assumed strictly positive (`0 < c e`), an implicit hypothesis
of the printed proof: its step "`c_{P′}(P′) < c(P′)` unless `P′ = P₁`" needs an arc of positive
cost in `P′ \ P₁`, and `c(P) = Σ c_e/W_e` is the undefined `0/0` on an unused zero-cost arc.
Minima are `Finset.inf` in `ℝ≥0∞`; `𝒫` is nonempty because it contains `P₁`. -/
theorem ineq_6_1 {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 < c e)
    (S S' : ι → Finset E) (i : ι) (hmove : IsBRMoveBy (singleCommodityGame D s t w c) i S S') :
    (pathsMeeting (stPaths D s t) (S i ∪ S' i)).inf
        (marginalCost (singleCommodityGame D s t w c) S') <
      (pathsMeeting (stPaths D s t) (S i ∪ S' i)).inf
        (marginalCost (singleCommodityGame D s t w c) S) := by sorry

end PriceOfStability.WeightedSingle

