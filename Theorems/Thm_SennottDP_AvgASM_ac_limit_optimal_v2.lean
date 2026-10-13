import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Theorem 8.1.1** (Sennott 1999, p. 169), corrected: (AC3) is used **uniformly**. The book states
(AC3) as `−Q ≤ liminf_{N→∞} r^N(i)` for each fixed `i`, but its proof uses the bound `r^N(i) ≥ −Q`
for all `i ∈ S_N` and `N ≥ N₀`; with only the pointwise `liminf` bound the statement is false
(a counterexample was accepted on prove2.me against `SennottDP.AvgASM.ac_limit_optimal`). The
hypothesis `hQ` adds that uniform bound; the conclusions are unchanged:
(i) `J* = lim_{N→∞} J^N` exists and is the minimum average cost in `Δ`: `J(i) = J*` for all `i`;
(ii) any limit point `e*` of a sequence `e^N` of stationary policies realizing the minimum in
(8.1) is average cost optimal for `Δ`. -/
theorem ac_limit_optimal_v2 {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : AS.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM

