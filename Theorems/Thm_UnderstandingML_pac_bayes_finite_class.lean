import Definitions.Def_UnderstandingML_PACBayes

open MeasureTheory


namespace UnderstandingML

/-- **Exercise 2** (p. 418). Suppose that `H` is a finite hypothesis class, set the prior to be
uniform over `H`, and set the posterior to be `Q(h_S) = 1` for some `h_S` and `Q(h) = 0` for all
other `h ∈ H`. Then `L_D(h_S) ≤ L_S(h_S) + √((ln|H| + ln(m/δ)) / (2(m − 1)))`: with probability
at least `1 − δ`, simultaneously for every `h ∈ H`. `m ≥ 2`, `[0, 1]`-valued measurable loss. -/
theorem pac_bayes_finite_class {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (H : Finset Hyp) (hH : H.Nonempty) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ h ∈ H,
      empRisk loss S h + Real.sqrt ((Real.log H.card + Real.log (m / δ)) / (2 * (m - 1))) <
        risk loss D h} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML

