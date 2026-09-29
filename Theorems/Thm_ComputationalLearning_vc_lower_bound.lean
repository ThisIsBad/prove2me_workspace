import Definitions.Def_ComputationalLearning_VC

open MeasureTheory


namespace ComputationalLearning

/-- **Theorem 3.5** (p. 62). Any algorithm for PAC learning a concept class of VC dimension `d`
must use `Ω(d/ε)` examples in the worst case. Stated with the two explicit forms of the proof
(pp. 62–64), for a class shattering some set of `d ≥ 1` points, on an instance space with
measurable singletons, and for every learning function `L` on samples of size `m`:
(i) if `m ≤ d/2`, some target concept in the class and some distribution make the error of
`L`'s hypothesis at least `1/8` with probability at least `1/2`;
(ii) if `ε ≤ 1/16` and `m ≤ (d − 1)/(64ε)`, some target concept and some distribution make the
error greater than `ε` with probability at least `1/4` (so a PAC algorithm with `δ < 1/4` needs
more than `(d − 1)/(64ε)` examples). -/
theorem vc_lower_bound {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : Set (X → Bool)) (d : ℕ) (hd1 : 1 ≤ d) (hd : (d : ℕ∞) ≤ vcDim C) (m : ℕ)
    (L : (Fin m → X × Bool) → X → Bool) :
    ((m : ℝ) ≤ d / 2 → ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
      ENNReal.ofReal (1 / 2) ≤ sampleLaw D c m {S | 1 / 8 ≤ errorOf D c (L S)}) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 → (m : ℝ) ≤ (d - 1) / (64 * ε) →
      ∃ c ∈ C, ∃ D : Measure X, IsProbabilityMeasure D ∧
        ENNReal.ofReal (1 / 4) ≤ sampleLaw D c m {S | ε < errorOf D c (L S)}) := by sorry

end ComputationalLearning

