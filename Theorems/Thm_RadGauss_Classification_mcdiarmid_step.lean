import Mathlib
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **McDiarmid step for the 0–1 loss** (Bartlett–Mendelson 2002, Appendix B, p. 480, second
display). With probability at least `1 − δ` over an i.i.d. sample `S ∼ P^n`, every `f ∈ F`
satisfies `P(Y ≠ f(X)) ≤ P̂_n(Y ≠ f(X)) + E sup_{h ∈ L∘F}(E h − Ê_n h) + √(ln(1/δ)/(2n))`.
The bad event (some `f ∈ F` violates the bound) has `P^n`-(outer) measure at most `δ`.
Measurability guard: the supremum `S ↦ gapSup P F S` is measurable (so its expectation is a
genuine Bochner integral of a bounded measurable function). -/
theorem mcdiarmid_step {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (classError P f ≤ trainError S f
            + (∫ S', gapSup P F S' ∂(Measure.pi fun _ : Fin n => P))
            + Real.sqrt (Real.log (1 / δ) / (2 * n)))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.Classification

