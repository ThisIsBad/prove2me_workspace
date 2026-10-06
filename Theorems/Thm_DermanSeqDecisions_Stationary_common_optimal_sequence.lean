import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal Topology
open SennottDP.AvgFinite Filter

namespace DermanSeqDecisions.Stationary

/-- One procedure `R* ∈ C″` is discount-optimal along a sequence `α_v → 1` (Derman, *On
Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962),
DOI 10.1287/mnsc.9.1.16, §2, proof of Theorem 1, p. 19, unnumbered). States `S` and decisions
`Act` are finite, every decision is available in every state, and the costs are nonnegative.
There are a deterministic stationary procedure `R*` (a map `f` from states to decisions) and a
sequence `α_v ∈ (0, 1)` with `α_v → 1` such that, for every `v`, `R*` is `α_v`-discount optimal:
`V_{R*}(i, α_v) ≤ V_R(i, α_v)` for every procedure `R ∈ C` and every initial state `i`.

**Formalization Note.** `V_R(i, α)` is `discCost θ α i ∈ [0, ∞]`, `C` is `Policy M` (all
history-dependent randomized procedures) and `C″` is `StationaryPolicy M`. The sequence is not
required to be monotone, as on the page. -/
theorem common_optimal_sequence {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ∃ f : StationaryPolicy M, ∃ αs : ℕ → ℝ,
      (∀ v, αs v ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto αs atTop (𝓝 1) ∧
      ∀ v, ∀ θ : Policy M, ∀ i : S,
        discCost f.toPolicy (αs v) i ≤ discCost θ (αs v) i := by sorry

end DermanSeqDecisions.Stationary

