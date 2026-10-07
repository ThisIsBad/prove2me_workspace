import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- A batch-size distribution (§3.1, p.118): probabilities `c_n = Pr{X = n}` of the number `X`
of customers in an arriving batch, supported on `{1, 2, …}` (`c_0 = 0`), nonnegative and
summing to one. -/
def IsBatchSizeDist (c : ℕ → ℝ) : Prop :=
  c 0 = 0 ∧ (∀ n : ℕ, 0 ≤ c n) ∧ HasSum c 1

/-- The rate-balance equations (3.1), p.118, of the `M^[X]/M/1` bulk-input queue with batch
arrival rate `λ`, service rate `μ` and batch-size probabilities `c_k`:
`0 = −(λ + μ)p_n + μp_{n+1} + λ ∑_{k=1}^{n} p_{n−k} c_k` for `n ≥ 1`, and `0 = −λp_0 + μp_1`. -/
def BulkInputBalance (lam mu : ℝ) (c p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
      0 = -(lam + mu) * p n + mu * p (n + 1) + lam * ∑ k ∈ Finset.Icc 1 n, p (n - k) * c k) ∧
    0 = -lam * p 0 + mu * p 1

/-- A steady-state solution of the `M^[X]/M/1` queue (book convention, §1.9 p.34 and the footnote
on p.118): a probability distribution `{p_n}` on `{0, 1, 2, …}` that solves (3.1). -/
def IsBulkInputSteadyState (lam mu : ℝ) (c p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p n) ∧ HasSum p 1 ∧ BulkInputBalance lam mu c p

/-- The generating function `∑_{n ≥ 0} p_n zⁿ` of a real sequence at a complex argument `z`
(p.118: `C(z) = ∑_{n=1}^∞ c_n zⁿ` and `P(z) = ∑_{n=0}^∞ p_n zⁿ`, `|z| ≤ 1`). -/
noncomputable def cpgf (p : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (p n : ℂ) * z ^ n

end QueueingFundamentals.AdvMarkov
