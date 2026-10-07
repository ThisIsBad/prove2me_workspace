import Mathlib
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 468, first display): with probability at least `1 − δ` over an i.i.d.
sample of size `n ≥ 1` from `P`, every `f ∈ F` satisfies
`E L(Y, f(X)) ≤ Ê_n φ(Y, f(X)) + E sup_{h ∈ φ̃∘F} (E h − Ê_n h) + √(8 ln(2/δ)/n)`.
The uniform deviation is assumed measurable as a function of the sample. -/
theorem combined_bound {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F))) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ ((∫ z, L z.2 (f z.1) ∂P) ≤
          empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (8 * Real.log (2 / δ) / n))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.RiskBound

