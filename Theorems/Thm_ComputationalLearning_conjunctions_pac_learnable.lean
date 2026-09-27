import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 1.2** (p. 16). The representation class of conjunctions of boolean literals is
(efficiently) PAC learnable, by the elimination algorithm: for every target conjunction `T` over
`x₁, …, xₙ`, every distribution `D` on `{0,1}ⁿ` and `ε, δ > 0`, the elimination hypothesis is
consistent with every sample labeled by `T`, and with `m ≥ (2n/ε)(ln(2n) + ln(1/δ))` examples it
has error greater than `ε` with probability at most `δ` (the bound of p. 17); hence conjunctions
are PAC learnable using conjunctions in the sample-complexity sense. -/
theorem conjunctions_pac_learnable {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * n / ε * (Real.log (2 * n) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalConj T) S →
      IsConsistent (evalConj (eliminate S)) S) ∧
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (conjunctionClass (Fin n)) (conjunctionClass (Fin n)) := by sorry

end ComputationalLearning
