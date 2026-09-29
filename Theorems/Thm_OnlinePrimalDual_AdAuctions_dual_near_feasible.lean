import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue

namespace OnlinePrimalDual.AdAuctions

/-- **Inequality (10.1)** (p. 213, PDF p. 124), a milestone en route to Theorem 10.1, proved there
by induction on the (relevant) iterations of the algorithm. `wonBids i` is the list, in allocation
order, of the bids of the items actually allocated to buyer `i` during the run; `hbids_valid`
records that every such bid is a genuine bid of this instance, bounded as `Rmax` requires
(`0 ≤ bd ≤ Rmax · B i`, from `hb_nonneg`/`hRmax_bound`). The conclusion is the book's own displayed
bound: buyer `i`'s final primal value is at least
`(1/(c−1)) · (c^{revenue(i)/B(i)} − 1)`, where `c = cParam inst`. -/
theorem dual_near_feasible {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (wonBids : I → List ℝ)
    (hbids_valid : ∀ i, ∀ bd ∈ wonBids i, 0 ≤ bd ∧ bd ≤ inst.Rmax * inst.B i) :
    ∀ i : I, buyerX inst i (wonBids i) ≥
      (1 / (cParam inst - 1)) * (cParam inst ^ (revenue inst wonBids i / inst.B i) - 1) := by sorry

end OnlinePrimalDual.AdAuctions
