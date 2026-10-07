import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_laplace

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- The Laplace transform of the M/M/1 busy-period CDF (§2.12, p.102). Let `p` be a probability
solution of the absorbing-barrier equations (`λ₀ = 0`) with `p₁(0) = 1`, so that `p₀(t)` is the
busy-period CDF. For every `s` with `Re s > 0`, `e^{-st} p₀(t)` is integrable on `(0, ∞)` and
`p̄₀(s) = 2μ / (s [λ + μ + s + r])`, where `r` is the square root of `(λ+μ+s)² - 4λμ` with
positive real part. -/
theorem busy_period_laplace (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (busyRHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = 1 then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s = 2 * (mu : ℂ) / (s * ((lam : ℂ) + (mu : ℂ) + s + r)) := by sorry

end QueueingFundamentals.Transient

