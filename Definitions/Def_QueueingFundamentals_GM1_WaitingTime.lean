import Mathlib

namespace QueueingFundamentals.GM1

/-- `Pr{n completions in ≤ t}` for exponential service at rate `μ` (§2.2.5, p.65): the Erlang
type-`n` CDF `∫_0^t μ(μx)^{n-1}/(n-1)! e^{-μx} dx` for `n ≥ 1`, and `1` for `n = 0` (no completion
is needed). -/
noncomputable def completionsCDF (mu : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, t => ∫ x in (0 : ℝ)..t,
      mu * (mu * x) ^ m / (Nat.factorial m : ℝ) * Real.exp (-mu * x)

/-- The FCFS line-delay CDF of an arriving customer (§2.2.5, p.65, with the arrival-point
probabilities `q_n`): `W_q(t) = q_0 + ∑_{n ≥ 1} Pr{n completions in ≤ t} q_n`. -/
noncomputable def lineDelayCDF (q : ℕ → ℝ) (mu t : ℝ) : ℝ :=
  ∑' n : ℕ, q n * completionsCDF mu n t

/-- The FCFS system-waiting-time CDF of an arriving customer: an arrival that finds `n` in the system
leaves after `n + 1` exponential service completions, so `W(t) = ∑_{n ≥ 0} Pr{n+1 completions in ≤ t} q_n`. -/
noncomputable def systemWaitCDF (q : ℕ → ℝ) (mu t : ℝ) : ℝ :=
  ∑' n : ℕ, q n * completionsCDF mu (n + 1) t

end QueueingFundamentals.GM1
