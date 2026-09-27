import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

/-- **Equation (5.2)** (§5.4.1, p. 113), the decomposition of `P_χ` in terms of quantities
estimable from the noisy oracle. For a statistical query `χ`, let `X₁` be the inputs on which
the label matters, `p₁ = Pr_{x ~ D}[x ∈ X₁]`, and `D₁` the distribution `D` restricted to `X₁`.
Then
`P_χ = p₁ · (Pr_{EX_CN(c, D₁)}[χ = 1] − η)/(1 − 2η) + Pr_{EX_CN(c, D)}[(χ = 1) ∧ (x ∈ X₂)]`,
where the first probability is under the noisy oracle on `D₁` (Equation (5.1) and the identity
`Pr_{EX_CN(c,D₁)}[χ = 1] = η + (1 − 2η) Pr_{EX(c,D₁)}[χ = 1]`) and the second under the noisy
oracle on `D` (on `X₂` a noisy label can replace the correct one). Stated for `0 ≤ η < 1/2`,
measurable `c` and `χ`; if `p₁ = 0` the conditional is the zero measure and the first term
vanishes. -/
theorem noisy_query_decomposition {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Bool) (hc : Measurable c) (χ : X × Bool → Bool)
    (hχ : Measurable χ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1 / 2) :
    queryProb D c χ =
      (D (labelSensitive χ)).toReal *
        ((noisyExampleLaw (D[|labelSensitive χ]) c η {p | χ p = true}).toReal - η) / (1 - 2 * η) +
      (noisyExampleLaw D c η {p | χ p = true ∧ p.1 ∉ labelSensitive χ}).toReal := by sorry

end ComputationalLearning

