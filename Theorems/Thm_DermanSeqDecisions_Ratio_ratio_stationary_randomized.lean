import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **The ratio criterion of a procedure in `C′` under Assumption A** (Derman, *On Sequential
Decisions and Markov Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16,
§4, unnumbered display, p. 23).

Let `w′ > 0`, `w″ > 0` be two cost sets, let `θ ∈ C′` choose decision `k` in state `s` with
probability `D_sk`, assume Assumption A, and let `π` satisfy (5) (p. 20) for the induced
transition matrix `p_sj = ∑_k q_sj(k) D_sk`. Then for every initial state `i`,
`ψ_θ(i) = (∑_s ∑_k π_s D_sk w′_sk) / (∑_s ∑_k π_s D_sk w″_sk)`.

**Formalization Note.** The page writes the summation index as `i`, the same letter as the
initial state; here it is `s`. (5) is stated as `π_j ≥ 0`, `π_j − ∑_s π_s p_sj = 0`,
`∑_j π_j = 1`. `M.C` plays no role. -/
theorem ratio_stationary_randomized {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a)
    (θ : Policy M) (D : S → Act → ℝ) (hD0 : ∀ s a, 0 ≤ D s a) (hD1 : ∀ s, ∑ a, D s a = 1)
    (hθ : IsStationaryRandomized θ D)
    (π : S → ℝ) (hπ0 : ∀ j, 0 ≤ π j)
    (hπ : ∀ j, π j - ∑ s, π s * inducedMatrix M D s j = 0) (hπ1 : ∑ j, π j = 1) (i : S) :
    ratioCost θ i w' w'' =
      (∑ s, ∑ a, π s * D s a * w' s a) / (∑ s, ∑ a, π s * D s a * w'' s a) := by sorry

end DermanSeqDecisions.Ratio

