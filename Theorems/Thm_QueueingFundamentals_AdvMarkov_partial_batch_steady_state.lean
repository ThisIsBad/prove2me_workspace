import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_BulkService

namespace QueueingFundamentals.AdvMarkov

/-- Eq. (3.9), p.124: for the partial-batch `M/M^[K]/1` queue with `λ < Kμ`, the characteristic
equation `μr^{K+1} − (λ + μ)r + λ = 0` of (3.8) has exactly one root `r_0` in `(0, 1)`, and the
steady-state solution of (3.7) is `p_n = (1 − r_0)r_0ⁿ` (`n ≥ 0`): this sequence is a probability
solution of (3.7), and every probability solution of (3.7) equals it. -/
theorem partial_batch_steady_state (lam mu : ℝ) (K : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hK : 1 ≤ K) (hstab : lam < (K : ℝ) * mu) :
    (∃! r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0) ∧
      ∀ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 → mu * r0 ^ (K + 1) - (lam + mu) * r0 + lam = 0 →
        IsPartialBatchSteadyState lam mu K (fun n : ℕ => (1 - r0) * r0 ^ n) ∧
          ∀ p : ℕ → ℝ, IsPartialBatchSteadyState lam mu K p →
            ∀ n : ℕ, p n = (1 - r0) * r0 ^ n := by sorry

end QueueingFundamentals.AdvMarkov

