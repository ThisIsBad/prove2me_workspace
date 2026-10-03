import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Theorem 8.1.1** (Sennott 1999, p. 169). Let `Δ` be an MDC on a countable state space `S` and
`(Δ_N)_{N ≥ N₀}` an approximating sequence for `Δ`. Assume that the (AC) assumptions hold for
the constants `J^N` and functions `r^N` of (AC1). Then:
(i) `J* = lim_{N→∞} J^N` exists and is the minimum average cost in `Δ`: `J(i) = J*` for all `i`;
(ii) any limit point `e*` of a sequence `e^N` of stationary policies realizing the minimum in
(8.1) is average cost optimal for `Δ`. -/
theorem ac_limit_optimal {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : AS.AC JN rN) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM
