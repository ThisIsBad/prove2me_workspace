import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_BulkInput

namespace QueueingFundamentals.AdvMarkov

/-- Eqs. (3.1), (3.3), (3.4), pp.118–119: the `M^[X]/M/1` bulk-input queue with batch arrival rate
`λ`, service rate `μ`, batch sizes `X` with `E[X] < ∞`, `r = λ/μ` and `ρ = λE[X]/μ < 1` has a
steady-state solution, and every steady-state solution has generating function
`P(z) = μp_0(1 − z)/(μ(1 − z) − λz[1 − C(z)])` for `|z| ≤ 1`, `z ≠ 1` (3.3), and
`p_0 = 1 − rE[X] = 1 − ρ`; if moreover `E[X²] < ∞`, its mean is
`L = r(E[X] + E[X²])/(2(1 − ρ)) = (ρ + rE[X²])/(2(1 − ρ))` (3.4). -/
theorem bulk_input_steady_state (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (EX EX2 r ρ : ℝ) (hEX : EX = ∑' n : ℕ, (n : ℝ) * c n)
    (hEX2 : EX2 = ∑' n : ℕ, (n : ℝ) ^ 2 * c n)
    (hr : r = lam / mu) (hρ : ρ = lam * EX / mu) (hρ1 : ρ < 1) :
    (∃ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p) ∧
      ∀ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p →
        (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          cpgf p z = (mu : ℂ) * (p 0 : ℂ) * (1 - z) /
            ((mu : ℂ) * (1 - z) - (lam : ℂ) * z * (1 - cpgf c z))) ∧
        p 0 = 1 - r * EX ∧ p 0 = 1 - ρ ∧
        (Summable (fun n : ℕ => (n : ℝ) ^ 2 * c n) →
          HasSum (fun n : ℕ => (n : ℝ) * p n) (r * (EX + EX2) / (2 * (1 - ρ))) ∧
          HasSum (fun n : ℕ => (n : ℝ) * p n) ((ρ + r * EX2) / (2 * (1 - ρ)))) := by sorry

end QueueingFundamentals.AdvMarkov

