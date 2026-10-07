import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_laplace

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- The Laplace transform of `p₀(t)` for the M/M/1 queue with `N(0) = i` (p.100):
for every probability solution `p` of the forward equations (2.72) with `p_n(0) = [n = i]`,
and every `s` with `Re s > 0`, `e^{-st} p₀(t)` is integrable on `(0, ∞)` and
`p̄₀(s) = z₁^{i+1} / (μ (1 - z₁))`, where `z₁ = (λ+μ+s - r)/(2λ)` and `r` is the square root of
`(λ+μ+s)² - 4λμ` with positive real part. -/
theorem mm1_laplace_p0 (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (mm1RHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = i then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s
        = (((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))) ^ (i + 1)
          / ((mu : ℂ) * (1 - ((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ)))) := by sorry

end QueueingFundamentals.Transient

