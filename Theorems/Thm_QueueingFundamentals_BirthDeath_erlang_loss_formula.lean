import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

/-- Eqs. (2.52)–(2.53), pp.81–82. The `M/M/c/c` queue is the birth–death process with
`λ_n = λ` for `n < c`, `λ_n = 0` for `n ≥ c` (§2.5), and the death rates (2.30). It has a
steady-state solution, and `{p_n}` is a steady-state solution exactly when
`p_n = ((λ/μ)^n/n!) / ∑_{i=0}^{c} (λ/μ)^i/i!` for `0 ≤ n ≤ c` and `p_n = 0` for `n > c`; in
particular the probability of a full system is `p_c = B(c, r)` with `r = λ/μ`. -/
theorem erlang_loss_formula (lam mu : ℝ) (c : ℕ) (r : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) :
    (∃ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p) ∧
      (∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, n ≤ c → p n = ((lam / mu) ^ n / (n.factorial : ℝ)) /
            ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ)) ∧
          ∀ n : ℕ, c < n → p n = 0)) ∧
      ∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p →
        p c = erlangB c r := by sorry

end QueueingFundamentals.BirthDeath

