import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **Theorem 5 (b)** (Bartlett–Mendelson 2002, p. 465). Let `P` be a probability distribution
on `X × {±1}`, `F` a set of `{±1}`-valued (measurable) functions on `X`, and
`(X_i, Y_i)_{i=1}^n ∼ P^n`. With probability at least `1 − δ`, every `f ∈ F` satisfies
`P(Y ≠ f(X)) ≤ P̂_n(Y ≠ f(X)) + R_n(F)/2 + √(ln(1/δ)/(2n))`,
where `R_n(F)` is the Rademacher complexity (Definition 2) of `F` as a class of real functions,
with respect to the marginal of `P` on `X`. The bad event (some `f ∈ F` violates the bound) has
`P^n`-(outer) measure at most `δ`. Added hypotheses: `0 < n`, `0 < δ < 1`, and the measurability
of the three random variables the proof integrates (`gapSup`, `ghostGapSup`, `R̂_n(F)`). -/
theorem theorem_5b {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ))
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (classError P f) ≤ ENNReal.ofReal (trainError S f)
            + rademacherComplexity (P.map Prod.fst) n (realClass F) / 2
            + ENNReal.ofReal (Real.sqrt (Real.log (1 / δ) / (2 * n))))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.Classification

