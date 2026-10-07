import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 468, last display), symmetrization:
`E sup_{h ∈ φ̃∘F} (E h − Ê_n h) ≤ R_n(φ̃∘F)` for an i.i.d. sample of size `n ≥ 1` from `P`.
The three random variables the argument integrates are assumed measurable: the uniform
deviation, the empirical Rademacher complexity of `φ̃∘F`, and the double-sample supremum
`(S, S') ↦ sup_{h ∈ φ̃∘F} ((1/n) Σ_i h(S'_i) − Ê_n h)`. -/
theorem symmetrization {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    ENNReal.ofReal
        (∫ S, supDev P n (phiTildeComp φ F) S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity P n (phiTildeComp φ F) := by sorry

end RadGauss.RiskBound

