import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
import Definitions.Def_SennottDP_DiscountedASM_tabooProb

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Lemma 4.7.3 (p. 78): operate `M` from `i` under the stationary policy `e` until
`S - S_N` is reached, and let `T_i(N)` be the length of this first passage; then
`lim_{N→∞} E_e[α^{T_i(N)}] = 0` (4.44), with `α^∞ = 0` (4.45). -/
theorem firstPassageDisc_tendsto_zero {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (e : S → Act) (he : ∀ i, e i ∈ M.A i) (i : S) :
    Tendsto (fun N => M.firstPassageDisc (Δs.SN N) e α i) atTop (𝓝 0) := by sorry

end SennottDP.DiscountedASM
