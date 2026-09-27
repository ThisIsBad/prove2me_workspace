import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory


namespace ComputationalLearning

/-- **§2.2, the improved sample size for conjunctions** (pp. 37–38). The elimination algorithm is
an Occam algorithm for conjunctions, and the hypothesis class it uses has at most `3ⁿ + 1`
concepts (each variable positive, negated or absent, plus the empty concept of a contradictory
conjunction); by Theorem 2.2, `m ≥ (1/ε)(ln(3ⁿ + 1) + ln(1/δ))`, i.e.
`O((1/ε) log(1/δ) + n/ε)`, examples suffice for error at most `ε` with confidence `1 − δ`, a
logarithmic improvement over the bound of Chapter 1. -/
theorem conjunctions_occam_bound {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log (3 ^ n + 1) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ := by sorry

end ComputationalLearning

