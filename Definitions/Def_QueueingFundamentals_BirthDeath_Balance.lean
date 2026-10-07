import Mathlib

namespace QueueingFundamentals.BirthDeath

/-- The product `∏_{i=1}^{n} λ_{i-1}/μ_i` of (2.3), p.51; it equals `1` for `n = 0`
(the empty product, as the book states on p.51). -/
noncomputable def bdProd (lam mu : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, lam (i - 1) / mu i

/-- The global balance equations (2.1), p.50, of the birth–death process with birth rates
`λ_n` (`n ≥ 0`) and death rates `μ_n` (`n ≥ 1`):
`(λ_n + μ_n) p_n = λ_{n-1} p_{n-1} + μ_{n+1} p_{n+1}` for `n ≥ 1`, and `λ_0 p_0 = μ_1 p_1`.
The value `mu 0` never enters. -/
def IsBalanced (lam mu : ℕ → ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
      (lam n + mu n) * p n = lam (n - 1) * p (n - 1) + mu (n + 1) * p (n + 1)) ∧
    lam 0 * p 0 = mu 1 * p 1

/-- A steady-state solution of the birth–death process (§1.9 and §2.1, pp.34, 50): a probability
distribution `{p_n}` on `{0, 1, 2, …}` (nonnegative, summing to one) that solves the balance
equations (2.1). -/
def IsSteadyState (lam mu : ℕ → ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p n) ∧ HasSum p 1 ∧ IsBalanced lam mu p

/-- The death rates (2.30), p.67, of the `M/M/c` queue: `μ_n = nμ` for `1 ≤ n < c` and `μ_n = cμ`
for `n ≥ c`, i.e. `μ_n = min(n, c) μ`. (Its value at `n = 0` is never used.) -/
noncomputable def mmcDeath (mu : ℝ) (c : ℕ) (n : ℕ) : ℝ :=
  ((min n c : ℕ) : ℝ) * mu

/-- The birth rates of a queue with truncation at `K` (§2.5, p.76): `λ_n = λ` for `n < K` and
`λ_n = 0` whenever `n ≥ K`. -/
noncomputable def truncArrival (lam : ℝ) (K : ℕ) (n : ℕ) : ℝ :=
  if n < K then lam else 0

/-- The death rates of the `M/M/∞` queue (§2.7, p.84): `μ_n = nμ` for all `n`. -/
noncomputable def infDeath (mu : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * mu

end QueueingFundamentals.BirthDeath
