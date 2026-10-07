import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Theorem 8** (p. 467). Let `L : 𝒴 × 𝒜 → [0, 1]` be a loss and `φ : 𝒴 × 𝒜 → [0, 1]` a cost
dominating it, `F` a class of maps `𝒳 → 𝒜`, and `(X_i, Y_i)_{i=1}^n` i.i.d. from the probability
measure `P` on `𝒳 × 𝒴`. For every `n ≥ 1` and `0 < δ < 1`, with probability at least `1 − δ`
every `f ∈ F` satisfies
`E L(Y, f(X)) ≤ Ê_n φ(Y, f(X)) + R_n(φ̃∘F) + √(8 ln(2/δ)/n)`,
where `φ̃∘F = {(x, y) ↦ φ(y, f(x)) − φ(y, 0) : f ∈ F}`. The probability of the bad event is an
outer measure. Measurability guard: the uniform deviation, the empirical Rademacher complexity
of `φ̃∘F` and the double-sample supremum are measurable functions of the sample(s). -/
theorem theorem_8 {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P) ≤
          ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
            rademacherComplexity P n (phiTildeComp φ F) +
            ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.RiskBound

