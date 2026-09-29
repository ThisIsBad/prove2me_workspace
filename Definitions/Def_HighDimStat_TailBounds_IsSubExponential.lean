import Mathlib

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Definition 2.7**, Wainwright, *High-Dimensional Statistics* (2019), p. 26. A random
variable `X` with mean `μ = E[X]` is sub-exponential with parameters `(ν, α)` (both
nonnegative) if `E[e^{λ(X-μ)}] ≤ e^{ν²λ²/2}` for all `|λ| < 1/α`, with the book's own
convention that `1/0` is interpreted as `+∞` (so `α = 0` recovers the unrestricted, sub-Gaussian
case). Realized as the disjunction `α = 0 ∨ |λ| < 1/α`, since Lean's real division gives
`1/0 = 0`, which would otherwise make the defining condition vacuous (never applicable) at
`α = 0` instead of unrestricted, exactly backwards from the book's stated convention.
Integrability of `X` and of every exponential moment on the allowed range of `λ` is required
explicitly to block the Bochner integral's junk value on a non-integrable function. -/
def IsSubExponential {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (Prob : Measure Ω)
    (nu alpha : ℝ) : Prop :=
  Integrable X Prob ∧
  (∀ lam : ℝ, (alpha = 0 ∨ |lam| < 1 / alpha) →
    Integrable (fun ω => Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob))) Prob) ∧
  (∀ lam : ℝ, (alpha = 0 ∨ |lam| < 1 / alpha) →
    ∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob ≤ Real.exp (nu ^ 2 * lam ^ 2 / 2))

end HighDimStat.TailBounds
