import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- A discount-optimal procedure in `C″` (Derman, *On Sequential Decisions and Markov Chains*,
Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §2, proof of Theorem 1,
pp. 18–19, unnumbered). States `S` and decisions `Act` are finite, every decision is available
in every state, and the costs `w_ik = M.C i k` are nonnegative. For every discount factor
`0 < α < 1` there is a deterministic stationary procedure `R_α ∈ C″` (a map `f` from states to
decisions) such that `V_{R_α}(i, α) ≤ V_R(i, α)` for every procedure `R ∈ C` (history-dependent
and randomized) and every initial state `i`, where `V_R(i, α) = ∑_t α^t W_t`.

**Formalization Note.** `V_R(i, α)` is `discCost θ α i ∈ [0, ∞]`; `C` is `Policy M` and `C″` is
`StationaryPolicy M` via `.toPolicy`. One `f` serves every initial state. `discCost` is defined
for every real `α`, so the range `0 < α < 1` is an explicit hypothesis. -/
theorem discount_optimal_stationary {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      discCost f.toPolicy α i ≤ discCost θ α i := by sorry

end DermanSeqDecisions.Stationary

