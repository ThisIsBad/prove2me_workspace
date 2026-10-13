import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria

open scoped ENNReal NNReal
open Filter

namespace SennottDP.SEN

/-- Sennott (1999), Proposition 7.1.1, p. 128: let `K` be a positive integer, `i` an initial
state and `θ` a policy with `v_{θ,K}(i) < ∞`. Then
`J_θ(i) = limsup_{n→∞} (1/(n − K)) E_θ[∑_{t=K}^{n-1} C(X_t,A_t) | X_0 = i]` (7.1).
The expectation of the sum is the sum of the expected costs `E_θ[C(X_t,A_t) | X_0 = i]`,
`K ≤ t < n`; the terms with `n ≤ K` (where `n − K = 0` in `ℕ`) do not affect the limit supremum. -/
theorem prop_7_1_1_average_cost_tail {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act)
    (K : ℕ) (hK : 0 < K) (i : S) (θ : SennottDP.Discounted.Policy M) (hfin : horizonCost M θ K i < ⊤) :
    avgCost M θ i =
      limsup (fun n : ℕ => (∑ t ∈ Finset.Ico K n, SennottDP.Discounted.expCost M θ i t) / ((n - K : ℕ) : ℝ≥0∞))
        atTop := by sorry

end SennottDP.SEN

