import Mathlib

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- The Laplace–Stieltjes transform `F*(s) = ∫ e^{-st} dF(t)` of a measure `μ` on `ℝ`, at a complex
argument `s`, integrated over all of `ℝ` (a Bochner integral: `0` where the integrand is not
integrable). For a distribution on `[0, ∞)` it is the book's `∫_0^∞ e^{-st} dF(t)`, used for `B*`,
`W*`, `W_q*`, `G*` in §§5.1.5–5.1.6 (pp.236–240) and for `A*` in §6.1; for the law of
`U = S − T` it is the two-sided LST `U*(s)` of §6.2 (p.285). -/
noncomputable def lst (μ : Measure ℝ) (s : ℂ) : ℂ :=
  ∫ t, Complex.exp (-(s * (t : ℂ))) ∂μ

/-- The `n`-fold convolution `G^{(n)}` of a measure `G` on `ℝ` with itself; `G^{(0)}` is the unit
mass at `0` (p.239). -/
noncomputable def convPow (G : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (convPow G n).conv G

/-- The busy-period equation (5.36) (p.239) for a candidate busy-period distribution `G`, in the
book's CDF form: for every `x`,
`G(x) = ∫_0^x ∑_{n ≥ 0} (e^{-λt}(λt)^n / n!) G^{(n)}(x - t) dB(t)`,
with `G(x) = G((-∞, x])` and the integral over `t ≤ x` (the service distribution `B` lives on
`[0, ∞)`). -/
def IsBusyPeriodEquation (lam : ℝ) (B G : Measure ℝ) : Prop :=
  ∀ x : ℝ, (G (Set.Iic x)).toReal =
    ∫ t in Set.Iic x,
      ∑' n : ℕ, Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) *
        ((convPow G n) (Set.Iic (x - t))).toReal ∂B

end QueueingFundamentals.MG1
