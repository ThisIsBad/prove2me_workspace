import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance

namespace OnlinePrimalDual.AdAuctions

/-- The total bid value `∑_j b(i,j)y(i,j)` accrued from buyer `i` over the run, i.e. the sum of
the bids of the items actually allocated to `i`, given as the list `wonBids i` in allocation
order — the book's own dual-profit quantity for buyer `i` (used throughout the proof of Theorem
10.1, e.g. inequality (10.1), p. 213). **`wonBids i` is precisely the items for which `i` was
actually charged**, not every item the argmax rule assigns to `i` (clarified per
`CHANGES_REQUESTED.md`'s non-blocking note, 2026-09-21 — see `buyerX`'s doc-comment for why the
distinction matters: step (2)'s "if `x(i) ≥ 1`, do nothing" means an assigned item need not be a
charged one). -/
noncomputable def revenue {I M : Type*} [Fintype I] [Fintype M]
    (_inst : AdAuctionsInstance I M) (wonBids : I → List ℝ) (i : I) : ℝ :=
  (wonBids i).sum

end OnlinePrimalDual.AdAuctions
