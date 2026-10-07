import Mathlib
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 467), the McDiarmid step: with probability at least `1 − δ/2` over
an i.i.d. sample of size `n ≥ 1` from `P`,
`sup_{h ∈ φ̃∘F} (E h − Ê_n h) ≤ E sup_{h ∈ φ̃∘F} (E h − Ê_n h) + √(2 ln(2/δ)/n)`.
The uniform deviation is assumed measurable as a function of the sample. -/
theorem mcdiarmid_step {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F))) :
    (Measure.pi fun _ : Fin n => P)
      {S | ¬ (supDev P n (phiTildeComp φ F) S ≤
          (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (2 * Real.log (2 / δ) / n))}
      ≤ ENNReal.ofReal (δ / 2) := by sorry

end RadGauss.RiskBound

