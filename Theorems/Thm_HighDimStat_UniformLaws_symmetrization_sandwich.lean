import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess

open MeasureTheory

namespace HighDimStat.UniformLaws

/-- **Proposition 4.11** (symmetrization sandwich), Wainwright, *High-Dimensional Statistics*
(2019), p. 107. For any convex non-decreasing `Φ : ℝ → ℝ`,
`E[Φ((1/2)‖Sₙ‖_F̄)] ≤ E[Φ(‖Pₙ-P‖_F)] ≤ E[Φ(2‖Sₙ‖_F)]`, where `F̄ = {f-E[f], f∈F}` is the
recentered function class. A hypothesis `hf` that each `f j` is measurable guards the Bochner
integrals against Mathlib's junk value on a non-integrable/non-measurable function. -/
theorem symmetrization_sandwich {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (eps : ℕ → Ω → ℝ)
    (n : ℕ) (Φ : ℝ → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hInt1 : Integrable (fun ω => Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω)) Prob)
    (hInt2 : Integrable (fun ω => Φ (empProcessDeviation f Xs X0 Prob n ω)) Prob)
    (hInt3 : Integrable (fun ω => Φ (2 * symmetrizedProcess f Xs eps n ω)) Prob) :
    ∫ ω, Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω) ∂Prob ≤
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob
    ∧
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob ≤
    ∫ ω, Φ (2 * symmetrizedProcess f Xs eps n ω) ∂Prob := by sorry

end HighDimStat.UniformLaws
