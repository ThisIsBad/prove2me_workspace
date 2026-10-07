import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace QueueingFundamentals.BirthDeath

/-- Eq. (2.33), p.68. In the steady state of the `M/M/c` queue with `ρ = λ/(cμ) < 1`, the expected
queue length `L_q = ∑_{n=c+1}^{∞} (n − c) p_n` is finite and equals `(r^c ρ / (c!(1 − ρ)^2)) p_0`,
where `r = λ/μ`. -/
theorem mmc_queue_length (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    HasSum (fun n : ℕ => if c + 1 ≤ n then ((n : ℝ) - c) * p n else 0)
      (r ^ c * ρ / ((c.factorial : ℝ) * (1 - ρ) ^ 2) * p 0) := by sorry

end QueueingFundamentals.BirthDeath

