import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter


namespace SennottDP.AvgASM

/-- **Proposition 8.7.1** (Sennott 1999, p. 194), corrected: (WAC3) is used **uniformly**. The
book states (WAC3₁) as `−Q(i) ≤ liminf_{N→∞} r^N(i)` for each fixed `i`, but the proof passes
to the limit in (8.1) by a Fatou argument that uses the bound `r^N(j) ≥ −Q(j)` for all `j ∈ S_N`
and all `N ≥ N₀`, together with (WAC3₂)(i) for the same `Q`; with only the pointwise `liminf`
bound the statement is false (the counterexample accepted on prove2.me against
`SennottDP.AvgASM.wac_limit_optimal`, which also refuted Theorem 8.1.1 as first stated; see
`ac_limit_optimal_v2`). The hypothesis `hQ` adds that uniform bound, for a nonnegative function
`Q` satisfying (WAC3₂)(i); the conclusions are unchanged:
`lim_{N→∞} J^N` exists and equals the (constant) minimum average cost `J(i)` of `Δ`, and any
limit point of a sequence of stationary policies realizing the minimum in (8.1) is average cost
optimal for `Δ`. -/
theorem wac_limit_optimal_v2 {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hWAC : AS.WAC JN rN)
    (hQ : ∃ Q : S → ℝ≥0,
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -(Q i : ℝ) ≤ rN N i) ∧
      ∀ e : StationaryPolicy M, ∀ i,
        Tendsto (fun N => ∑ j ∈ AS.SN N, AS.PN N i (e.f i) j * (Q j : ℝ≥0∞)) atTop
          (𝓝 (∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞))) ∧
        ∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞) < ⊤) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM

