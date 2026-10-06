import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_DermanSeqDecisions_Stationary_totalCost

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- Theorem 1 (Derman, *On Sequential Decisions and Markov Chains*, Management Science
9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §2, p. 18, Theorem 1, (1) and (2)). States `S`
(Derman's `0, …, L`) and decisions `Act` (Derman's `d_1, …, d_K`) are finite, every decision is
available in every state, `M.P i k j = q_ij(k)` and `M.C i k = w_ik`.

1. (Problem 1) If `w_ik > 0` for all `i, k`, there is a deterministic stationary procedure
   `R₁ ∈ C″` with `Q_{R₁}(i) = min_{R ∈ C} Q_R(i)` for every `i`.
2. (Problem 2) If a state `L` is absorbing under every decision, `w_Lk = 0` for all `k`, and
   `w_ik > 0` for `i ≠ L`, there is a deterministic stationary procedure `R₂ ∈ C″` with
   `S_{R₂}(i) = min_{R ∈ C} S_R(i)` (possibly `∞`) for every `i`.

**Formalization Note.** `C` is `Policy M` (all history-dependent randomized procedures) and `C″`
is `StationaryPolicy M` via `.toPolicy`; "min attained by `R₁`" is `Q_{R₁}(i) ≤ Q_R(i)` for every
`R` and `i`, with one `R₁` for all initial states. `Q_R(i)` is `avgCost θ i =
limsup_n (∑_{t<n} W_t)/n`; Derman's `limsup_T (1/T) ∑_{t=0}^T W_t` has the same value because
`W_t` is bounded by `max w_ik`. `S_R(i)` is `totalCost θ i ∈ [0, ∞]`. "L absorbing for all
`R ∈ C`" is `M.P L a L = 1` for every decision `a`, as every decision is used by some procedure.
Derman states `w_ik > 0` for all `i` and also `w_Lk = 0`; Problem 2 is read with `w_ik > 0` only
for `i ≠ L`. The two problems carry their own cost hypotheses, in separate implications. -/
theorem theorem_1 {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ((∀ i a, 0 < M.C i a) →
      ∃ R₁ : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
        avgCost R₁.toPolicy i ≤ avgCost θ i) ∧
    (∀ L : S, (∀ a, M.P L a L = 1) → (∀ a, M.C L a = 0) → (∀ i a, i ≠ L → 0 < M.C i a) →
      ∃ R₂ : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
        totalCost R₂.toPolicy i ≤ totalCost θ i) := by sorry

end DermanSeqDecisions.Stationary

