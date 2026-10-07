import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_MDc

namespace QueueingFundamentals.GG1

/-- Eq. (6.18) (p.295) for the M/D/c queue (`c` servers, constant service time taken as the unit of
time, Poisson arrivals at rate `λ > 0` per unit). Under the steady-state condition `λ < c` a
probability solution of (6.17) exists; and for every probability solution `p` of (6.17) and every
`|z| ≤ 1`,
`P(z)(1 − z^c e^{λ(1−z)}) = ∑_{n=0}^{c} p_n z^n − P_c z^c = ∑_{n=0}^{c−1} p_n (z^n − z^c)`,
the cleared-denominator form of `P(z) = (∑_{n=0}^{c} p_n z^n − P_c z^c)/(1 − z^c e^{λ(1−z)})`. -/
theorem mdc_pgf (lam : ℝ) (hlam : 0 < lam) (c : ℕ) (hc : 1 ≤ c) :
    ((lam < c) → ∃ p : ℕ → ℝ, IsMDcStationary lam c p) ∧
    ∀ p : ℕ → ℝ, IsMDcStationary lam c p → ∀ z : ℂ, ‖z‖ ≤ 1 →
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          (∑ n ∈ Finset.range (c + 1), (p n : ℂ) * z ^ n) - (cumProb p c : ℂ) * z ^ c ∧
      QueueingFundamentals.MG1.pgf p z * (1 - z ^ c * Complex.exp ((lam : ℂ) * (1 - z))) =
          ∑ n ∈ Finset.range c, (p n : ℂ) * (z ^ n - z ^ c) := by sorry

end QueueingFundamentals.GG1

