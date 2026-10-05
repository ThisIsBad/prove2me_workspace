import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **Theorem 3** (Derman, *On Sequential Decisions and Markov Chains*, Management Science
9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, p. 23): "Under assumption A, there exists a
procedure `R₃ ε C″` such that `ψ_{R₃}(i) = min_{R ε C} ψ_R(i)`."

Let `w′ > 0` and `w″ > 0` be two sets of expected costs and assume Assumption A (every
stationary randomized procedure makes all states communicate). Then for every initial state `i`
there is a deterministic stationary procedure `f ∈ C″` whose ratio criterion
`ψ_f(i) = lim sup_T (∑_{t≤T} W′_t)/(∑_{t≤T} W″_t)` is at most `ψ_θ(i)` for every procedure
`θ ∈ C`; in particular the minimum over `C` is attained.

**Formalization Note.** The quantifier order is `∀ i, ∃ f`, as in the proof ("Suppose `X₀ = i`
with probability 1 …"). The competitors `θ` range over all history-dependent randomized
procedures (`Policy M`). `hA` says all decisions are available in every state. Assumption A
is kept because the theorem states it. `M.C` plays no role; the costs are `w′`, `w″`. -/
theorem theorem_3 {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (hAssA : AssumptionA M)
    (w' w'' : S → Act → ℝ) (hw' : ∀ s a, 0 < w' s a) (hw'' : ∀ s a, 0 < w'' s a) :
    ∀ i : S, ∃ f : StationaryPolicy M, ∀ θ : Policy M,
      ratioCost f.toPolicy i w' w'' ≤ ratioCost θ i w' w'' := by sorry

end DermanSeqDecisions.Ratio

