import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

open scoped ENNReal

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, proof, p. 1620 (PDF p. 19): "Observe that if player i
currently uses path P, then i's payment is w_i c(P)."

In the weighted single-commodity game with weights `wᵢ ≥ 1` and arc costs `c_e ≥ 0`, for every
strategy profile `S` and every player `i`, the payment of `i` equals `wᵢ · c_S(Sᵢ)`, where
`c_S(P) = Σ_{e∈P} c_e/W_e` is the marginal cost of the path `P` in the state `S`.

**Formalization Note.** `c(P)` is valued in `ℝ≥0∞` (see `marginalCost`), so the identity is stated
after embedding the real payment by `ENNReal.ofReal`; on the arcs of `Sᵢ` every `W_e ≥ wᵢ ≥ 1`, so
all terms are finite. The paper's standing assumption `c_e ≥ 0` (Sect. 2) suffices here; the
positivity of costs that the later steps of the proof need is not assumed. -/
theorem payment_eq_weight_mul_marginalCost {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard)
    (S : ι → Finset E) (hS : IsProfile (singleCommodityGame D s t w c) S) (i : ι) :
    ENNReal.ofReal (payment (singleCommodityGame D s t w c) S i) =
      ENNReal.ofReal (w i) * marginalCost (singleCommodityGame D s t w c) S (S i) := by sorry

end PriceOfStability.WeightedSingle

