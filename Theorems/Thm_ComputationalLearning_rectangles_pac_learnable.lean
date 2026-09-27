import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory


namespace ComputationalLearning

/-- **Theorem 1.1** (p. 12). The concept class of axis-aligned rectangles over the Euclidean
plane is (efficiently) PAC learnable, by the tightest-fit algorithm: for every target rectangle,
every distribution `D` on the plane and `ε, δ > 0`, the tightest-fit rectangle is consistent with
every sample labeled by the target, and with `m ≥ (4/ε) ln(4/δ)` examples it has error greater
than `ε` with probability at most `δ` (§1.1, p. 6); hence rectangles are PAC learnable using
rectangles in the sample-complexity sense. -/
theorem rectangles_pac_learnable (a b : ℝ × ℝ) (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 4 / ε * Real.log (4 / δ) ≤ m) :
    (∀ S : Fin m → (ℝ × ℝ) × Bool, IsLabeledBy (rectConcept a b) S →
      IsConsistent (tightestFit S) S) ∧
    sampleLaw D (rectConcept a b) m {S | ε < errorOf D (rectConcept a b) (tightestFit S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable rectangleClass rectangleClass := by sorry

end ComputationalLearning

