import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_mmInfTransient

namespace QueueingFundamentals.Transient

/-- (2.77) and the M/M/∞ transient law (p.101). For `λ, μ > 0` and `N(0) = 0`:
the functions `p_n(t) = (1/n!) ((1 - e^{-μt}) λ/μ)^n exp(-(1 - e^{-μt}) λ/μ)` solve the forward
equations (2.76) on `[0, ∞)`, satisfy `p_n(0) = [n = 0]`, form a probability distribution for
every `t ≥ 0`, have generating function
`P(z, t) = ∑ p_n(t) zⁿ = exp((z - 1)(1 - e^{-μt}) λ/μ)` for `|z| ≤ 1`, and are the only
probability solution of (2.76) with that initial condition. -/
theorem mmInf_transient (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    IsForwardSolution (mmInfRHS lam mu) (mmInfTransient lam mu) ∧
      (∀ n : ℕ, mmInfTransient lam mu n 0 = if n = 0 then 1 else 0) ∧
      IsProbabilityFamily (mmInfTransient lam mu) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, ‖z‖ ≤ 1 →
        HasSum (fun n : ℕ => (mmInfTransient lam mu n t : ℂ) * z ^ n)
          (Complex.exp ((z - 1) * ((1 - Real.exp (-mu * t)) * (lam / mu) : ℝ)))) ∧
      ∀ q : ℕ → ℝ → ℝ, IsForwardSolution (mmInfRHS lam mu) q → IsProbabilityFamily q →
        (∀ n : ℕ, q n 0 = if n = 0 then 1 else 0) →
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q n t = mmInfTransient lam mu n t := by sorry

end QueueingFundamentals.Transient

