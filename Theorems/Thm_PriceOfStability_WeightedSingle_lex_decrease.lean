import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

open scoped ENNReal

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, proof, p. 1620 (PDF p. 19): "the cheapest improving
deviation of any player causes P(S) to strictly decrease lexicographically."

In the weighted single-commodity game with weights `wᵢ ≥ 1` and positive arc costs, let `P(S)` be
the list of the marginal costs `c_S(P)` of all simple `s`–`t` paths `P`, sorted in increasing
order. If `S'` arises from `S` by a best-response move of some player, then `P(S')` is strictly
smaller than `P(S)` in the lexicographic order.

**Formalization Note.** Arc costs are assumed strictly positive (`0 < c e`), an implicit hypothesis
of the printed proof (see `ineq_6_1`). `List.Lex (· < ·) l₁ l₂` is the strict lexicographic order
"`l₁` comes before `l₂`"; the two lists have the same length (the number of paths). -/
theorem lex_decrease {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 < c e)
    (S S' : ι → Finset E) (hmove : IsBRMove (singleCommodityGame D s t w c) S S') :
    List.Lex (· < ·) (sortedCosts (singleCommodityGame D s t w c) (stPaths D s t) S')
      (sortedCosts (singleCommodityGame D s t w c) (stPaths D s t) S) := by sorry

end PriceOfStability.WeightedSingle

