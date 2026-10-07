import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory

namespace RadGauss.Classification

/-- **Symmetrization for the 0–1 loss** (Bartlett–Mendelson 2002, Appendix B, p. 480, third
display, corrected): `E sup_{h ∈ L∘F} (E h − Ê_n h) ≤ R_n(F)/2`, where `L(Y, f(X)) = 1(Y ≠ f(X))`
and `R_n(F)` is the Rademacher complexity (Definition 2, with the absolute value) of the real
class `F ⊆ {±1}^X` with respect to the marginal of `P` on `X`. The paper prints the last step of
its chain as an equality; it is only an inequality (for `F = {f}` the left side of that step is
`0` while `R_n(F)/2 > 0`), and the chain's conclusion is stated with `≤`.
Measurability guards: `S ↦ sup_f (P(Y ≠ f(X)) − P̂_n(Y ≠ f(X)))`, the double-sample supremum
`(S, S') ↦ sup_f (P̂'_n − P̂_n)(Y ≠ f(X))`, and `x ↦ R̂_n(F)(x)` are measurable. -/
theorem symmetrization {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    ENNReal.ofReal (∫ S, gapSup P F S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity (P.map Prod.fst) n (realClass F) / 2 := by sorry

end RadGauss.Classification

