import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy

open MeasureTheory

namespace HighDimStat.Concentration

/-- **Proposition 3.2** (Herbst argument), Wainwright, *High-Dimensional Statistics* (2019),
p. 60. Suppose that the entropy `H(e^{λX})` satisfies `H(e^{λX}) ≤ (1/2)σ²λ²φ_X(λ)` for all
`λ ∈ I`, where `I` is either `[0,∞)` or `ℝ`. Then `X` satisfies
`log E[e^{λ(X-E[X])}] ≤ (1/2)λ²σ²` for all `λ ∈ I`. -/
theorem herbst_argument {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X : Ω → ℝ) (sigma : ℝ) (I : Set ℝ)
    (hI : I = Set.Ici 0 ∨ I = Set.univ)
    (hInt : ∀ lam ∈ I, Integrable (fun ω => Real.exp (lam * X ω)) Prob ∧
      Integrable (fun ω => Real.exp (lam * X ω) * Real.log (Real.exp (lam * X ω))) Prob)
    (hEntropy : ∀ lam ∈ I,
      phiEntropy (fun ω => Real.exp (lam * X ω)) Prob ≤
        1 / 2 * sigma ^ 2 * lam ^ 2 * ∫ ω, Real.exp (lam * X ω) ∂Prob) :
    ∀ lam ∈ I,
      Real.log (∫ ω, Real.exp (lam * (X ω - ∫ ω', X ω' ∂Prob)) ∂Prob) ≤
        1 / 2 * lam ^ 2 * sigma ^ 2 := by sorry

end HighDimStat.Concentration

