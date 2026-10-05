import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **Theorem 1 (1) for costs of either sign** (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, proof of Theorem 3,
p. 23, using Theorem 1 (1), p. 18): "the hypothesis that `w_ik > 0` is unnecessary for Problem 1".

For every real cost function `c` there is a deterministic stationary procedure `f ∈ C″` whose
long-run average expected cost `Q_f(i)` is at most `Q_θ(i)` for every procedure `θ ∈ C` and
every initial state `i`; one `f` serves every initial state.

**Formalization Note.** `M.P` is Derman's `q_ij(k)`; `hA` says all decisions are available in
every state. The competitors `θ` range over all history-dependent randomized procedures
(`Policy M`). The cost `c` is an explicit argument with no sign condition; `M.C` plays no role. -/
theorem theorem_1_signed {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (c : S → Act → ℝ) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      avgCostR f.toPolicy i c ≤ avgCostR θ i c := by sorry

end DermanSeqDecisions.Ratio

