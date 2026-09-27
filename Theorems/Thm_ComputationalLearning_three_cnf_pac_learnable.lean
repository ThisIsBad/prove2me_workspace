import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory


namespace ComputationalLearning

/-- **Theorem 1.4** (p. 24). The representation class of 3-CNF formulae is (efficiently) PAC
learnable, by running the elimination algorithm over the `(2n)³` expanded variables
`y_{u,v,w} = u ∨ v ∨ w`: for every target 3-CNF formula `F`, every distribution `D` on `{0,1}ⁿ`
and `ε, δ > 0`, the hypothesis is consistent with every sample labeled by `F`, is itself a 3-CNF
formula, and with `m ≥ (2N/ε)(ln(2N) + ln(1/δ))` examples, `N = (2n)³`, has error greater than
`ε` with probability at most `δ` (the transformation of instances is one-to-one, so the error
is preserved, p. 24); hence 3-CNF formulae are PAC learnable using 3-CNF formulae. -/
theorem three_cnf_pac_learnable {n : ℕ} (F : ThreeCNF n) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * (Fintype.card (Clause n) : ℝ) / ε *
      (Real.log (2 * Fintype.card (Clause n)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalThreeCNF F) S →
      IsConsistent (learnThreeCNF S) S) ∧
    (∀ S : Fin m → Cube (Fin n) × Bool, learnThreeCNF S ∈ threeCNFClass n) ∧
    sampleLaw D (evalThreeCNF F) m {S | ε < errorOf D (evalThreeCNF F) (learnThreeCNF S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (threeCNFClass n) (threeCNFClass n) := by sorry

end ComputationalLearning

