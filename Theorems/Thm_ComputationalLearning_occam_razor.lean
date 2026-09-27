import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory


namespace ComputationalLearning

/-- **Theorem 2.1 (Occam's Razor)** (p. 34). Let `L` be an `(α, β)`-Occam algorithm for `C`
using `H`: on a sample of `m` examples labeled by `c ∈ Cₙ` it outputs a representation (a binary
string) of a hypothesis consistent with the sample of bit length at most `(n · size(c))^α m^β`,
`α ≥ 0`, `0 ≤ β < 1`. Then there is a constant `a > 0` such that if `L` is given a random sample of
`m ≥ a((1/ε) log(1/δ) + ((n · size(c))^α/ε)^{1/(1−β)})` examples, with probability at least
`1 − δ` its hypothesis has error at most `ε`. Stated with the explicit sufficient conditions
`m ≥ (2/ε) ln(1/δ)`, `m ≥ 4 ln 2/ε` and `m^{1−β} ≥ (4 ln 2/ε)(n s)^α`, where `s` bounds
`size(c)` (they make `2^{K+1}(1 − ε)^m ≤ δ` for `K = (n s)^α m^β`, the number of binary strings
of length at most `K` being less than `2^{K+1}`). -/
theorem occam_razor {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (R : List Bool → X → Bool)
    (hR : ∀ r, Measurable (R r)) (n s : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (L : (Fin m → X × Bool) → List Bool)
    (hcons : ∀ S, IsLabeledBy c S → IsConsistent (R (L S)) S)
    (hsize : ∀ S, IsLabeledBy c S →
      ((L S).length : ℝ) ≤ ((n * s : ℕ) : ℝ) ^ α * (m : ℝ) ^ β)
    (hm1 : 2 / ε * Real.log (1 / δ) ≤ m) (hm2 : 4 * Real.log 2 / ε ≤ m)
    (hm3 : 4 * Real.log 2 / ε * ((n * s : ℕ) : ℝ) ^ α ≤ (m : ℝ) ^ (1 - β)) :
    sampleLaw D c m {S | ε < errorOf D c (R (L S))} ≤ ENNReal.ofReal δ := by sorry

end ComputationalLearning

