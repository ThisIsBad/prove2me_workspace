import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

/-- Eqs. (2.37)–(2.38), p.69. In the steady state of the `M/M/c` queue with `r = λ/μ` and
`ρ = r/c < 1`, the probability `W_q(0) = ∑_{n=0}^{c−1} p_n` of at most `c − 1` customers in the
system equals `1 − r^c p_0 / (c!(1 − ρ))`, and its complement `1 − W_q(0)` is the Erlang-C
formula `C(c, r)`. -/
theorem erlang_c_formula (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    ∑ n ∈ Finset.range c, p n = 1 - r ^ c * p 0 / ((c.factorial : ℝ) * (1 - ρ)) ∧
      1 - ∑ n ∈ Finset.range c, p n = erlangC c r := by sorry

end QueueingFundamentals.BirthDeath

