import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- The stochastic balance equations (3.7), p.124, of the partial-batch `M/M^[K]/1` bulk-service
queue (§3.2.0.1): Poisson arrivals at rate `λ`, one server that serves up to `K` customers at a
time, exponential batch service at rate `μ`:
`0 = −(λ + μ)p_n + μp_{n+K} + λp_{n−1}` for `n ≥ 1`, and
`0 = −λp_0 + μp_1 + μp_2 + ⋯ + μp_{K−1} + μp_K`. -/
def PartialBatchBalance (lam mu : ℝ) (K : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → 0 = -(lam + mu) * p n + mu * p (n + K) + lam * p (n - 1)) ∧
    0 = -lam * p 0 + mu * ∑ k ∈ Finset.Icc 1 K, p k

/-- A steady-state solution of the partial-batch `M/M^[K]/1` queue (book convention, §1.9 p.34
and the footnote on p.118): a probability distribution on `{0, 1, 2, …}` that solves (3.7). -/
def IsPartialBatchSteadyState (lam mu : ℝ) (K : ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p n) ∧ HasSum p 1 ∧ PartialBatchBalance lam mu K p

end QueueingFundamentals.AdvMarkov
