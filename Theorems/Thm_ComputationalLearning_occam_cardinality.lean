import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory


namespace ComputationalLearning

/-- **Theorem 2.2 (Occam's Razor, cardinality version)** (p. 35). Let `H` be a finite hypothesis
class. For any target concept `c`, any distribution `D` and `0 < ε ≤ 1`: the probability that a
random sample of `m` examples is consistent with some hypothesis of `H` of error greater than
`ε` is at most `|H|(1 − ε)^m`; consequently, if `m ≥ (1/ε)(ln|H| + ln(1/δ))` it is at most `δ`,
and any algorithm that outputs a hypothesis in `H` consistent with its sample has error greater
than `ε` with probability at most `|H|(1 − ε)^m` (the book's constant `b` is `1` with natural
logarithms, from `(1 − ε)^m ≤ e^{−εm}`). -/
theorem occam_cardinality {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (H : Finset (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ) :
    sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤
      ENNReal.ofReal (H.card * (1 - ε) ^ m) ∧
    (1 / ε * (Real.log H.card + Real.log (1 / δ)) ≤ m →
      sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤ ENNReal.ofReal δ) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (H.card * (1 - ε) ^ m)) := by sorry

end ComputationalLearning

