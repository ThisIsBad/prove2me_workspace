import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- Derman's expected total cost `S_R(i) = ∑_{t=0}^∞ W_t` of Problem 2
(Derman, *On Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962),
DOI 10.1287/mnsc.9.1.16, §1, p. 17, Problem 2): the sum over all times `t` of the expected cost
`W_t = E_θ[w(X_t, Δ_t) | X_0 = i]` incurred at time `t` by the procedure `θ` started in state `i`.

**Formalization Note.** `W_t` is `SennottDP.AvgFinite.expCost θ i t`. The sum is taken in
`[0, ∞]` (`ℝ≥0∞`), so that, as on p. 18, `S_R(i)` may be `∞`; it is never a real `tsum` with a
default value `0`. It coincides with `discCost θ 1 i`; it is given its own name because the paper
treats it as its own criterion. -/
noncomputable def totalCost {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (θ : Policy M) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, expCost θ i t

end DermanSeqDecisions.Stationary
