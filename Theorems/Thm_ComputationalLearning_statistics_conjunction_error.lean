import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

/-- **Learning conjunctions from statistics** (§5.2, p. 107; the analysis behind Theorem 5.2). For
a target conjunction `c` over `x₁, …, xₙ`, a distribution `D` and `ε > 0`, if `h` is the
conjunction of all the significant literals (`p₀(z) ≥ ε/8n`) that are not harmful
(`p₀₁(z) < ε/8n`), then `error(h) ≤ ε/4 + ε/4 = ε/2`: a false positive requires an insignificant
literal of `c` to be `0`, a false negative a harmful literal of `h` to be `0` on a positive
example, and the union bound over the `2n` literals gives `ε/4` each. -/
theorem statistics_conjunction_error {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) :
    errorOf D (evalConj T) (evalConj (statisticsConj D (evalConj T) ε)) ≤ ε / 2 := by sorry

end ComputationalLearning

