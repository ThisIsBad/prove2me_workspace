import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Implicit

/-- **(9.16)** (Goldie 1991, Ann. Appl. Probab. 1(1), §9, proof of Theorem 2.3, Case 2b, p. 148).
Suppose `M` satisfies the conditions of Lemma 2.2 and `M ≤ 0` a.s., `M′` has the law of `M`, and
`R, M, M′` are independent. If (2.8) and (2.9) hold, then
`∫₀^∞ |P(R > t) − P(MM′R > t)| t^{κ−1} dt < ∞`.

**Formalization Note** The conclusion is (2.8) for the multiplier `MM′` in place of `M`
(`TailCondPlus P (M·M′) R κ`, integrability of the signed integrand on `(0, ∞)`). The copy `M′` is
assumed on the given probability space (the paper's "common probability space", p. 144):
the statement quantifies over every space carrying such `R, M, M′`. -/
theorem eq_9_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M M' R : Ω → ℝ) (hM : Measurable M) (hM' : Measurable M') (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hident : IdentDistrib M' M P P)
    (hind : iIndepFun (fun i : Fin 3 => (![R, M, M'] : Fin 3 → Ω → ℝ) i) P)
    (hM_nonpos : ∀ᵐ ω ∂P, M ω ≤ 0)
    (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ) :
    TailCondPlus P (fun ω => M ω * M' ω) R κ := by sorry

end GoldieRenewal.Implicit

