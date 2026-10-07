import Mathlib
import Definitions.Def_BurkholderDFI_ConcavePhi_Partial

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConcavePhi

/-- §20, proof of Theorem 20.1, p. 38: with `τ = inf {n ≥ 0 : W_{n+1} > λ}`,
`Z ∧ λ ≤ Z_τ + λI(τ < ∞)` pointwise,
`EZ_τ = E Σ I(τ ≥ k) z_k = E Σ I(τ ≥ k) E(z_k|𝒜_{k−1}) = EW_τ ≤ E(W ∧ λ)` and
`E[λ I(τ < ∞)] = λ P(W > λ) ≤ E(W ∧ λ)`. -/
theorem stopped_sum_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) (l : ℝ≥0) (hl : 0 < l) :
    (∀ ω, min (Zpart z ⊤ ω) (l : ℝ≥0∞) ≤ Zpart z (stopIdx ℱ P z l ω) ω
        + Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω) ∧
    (∫⁻ ω, Zpart z (stopIdx ℱ P z l ω) ω ∂P = ∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P) ∧
    (∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) ∧
    (∫⁻ ω, Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω ∂P
        = (l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}) ∧
    ((l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}
        ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) := by sorry

end BurkholderDFI.ConcavePhi

