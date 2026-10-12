import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GoldieRenewal.Implicit

/-- **Lemma 2.2** (Goldie, *Implicit renewal theory and tails of solutions of random equations*,
Ann. Appl. Probab. 1(1):126–166 (1991), p. 129). Let `M` be a random variable such that, for some
`κ > 0`, (2.3) `E|M|^κ = 1`, (2.4) `E|M|^κ log⁺|M| < ∞` and (2.5) the conditional law of `log|M|`
given `M ≠ 0` is nonarithmetic. Then (2.6) `−∞ ≤ E log|M| < 0` and (2.7)
`m := E|M|^κ log|M| ∈ (0, ∞)`.

**Formalization Note** The hypotheses are `CramerConditions κ (P.map M)` (the law of `M`).
(2.6) is stated as: `E log⁺|M| < ∞` (so `E log|M| = E log⁺|M| − E log⁻|M|` is a well-defined element
of `[−∞, ∞)`, with `log 0 = −∞`), and this extended real is `< 0`; the value `−∞` is allowed, as in
the paper. (2.7) is stated as integrability of `|M|^κ log|M|` (finiteness) together with `0 < m`. -/
theorem lemma_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (κ : ℝ) (hC : CramerConditions κ (P.map M)) :
    (logPlusMoment (P.map M) < ∞ ∧ logAbsMean (P.map M) < 0) ∧
      (Integrable (fun x : ℝ => |x| ^ κ * Real.log |x|) (P.map M) ∧
        0 < cramerMean κ (P.map M)) := by sorry

end GoldieRenewal.Implicit

