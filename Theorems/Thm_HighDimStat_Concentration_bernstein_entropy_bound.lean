import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy

open MeasureTheory

namespace HighDimStat.Concentration

/-- **Proposition 3.3** (Bernstein entropy bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 61. Suppose there are positive constants `b, σ` such that
`H(e^{λX}) ≤ λ²{b φ_X'(λ) + φ_X(λ)(σ²-bE[X])}` for all `λ ∈ [0,1/b)`. Then `X` satisfies
`log E[e^{λ(X-E[X])}] ≤ σ²λ²(1-bλ)⁻¹` for all `λ ∈ [0,1/b)`. -/
theorem bernstein_entropy_bound {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (b sigma : ℝ) (hb : 0 < b) (hsigma : 0 < sigma)
    (hInt : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        lam ^ 2 * (b * deriv (fun l : ℝ => ∫ ω, Real.exp (l * X ω) ∂Prob) lam +
          (∫ ω, Real.exp (lam * X ω) ∂Prob) * (sigma ^ 2 - b * ∫ ω, X ω ∂Prob))) :
    ∀ lam : ℝ, 0 ≤ lam → lam < 1 / b →
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        sigma ^ 2 * lam ^ 2 * (1 - b * lam)⁻¹ := by sorry

end HighDimStat.Concentration

