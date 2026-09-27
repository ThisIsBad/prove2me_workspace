import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory


namespace ComputationalLearning

/-- **Theorem 2.3** (p. 43). For any fixed `k ≥ 1`, the representation class of `k`-decision lists
over `n ≥ 1` variables is (efficiently) PAC learnable, by the greedy decision-list algorithm: on a sample labeled by a
`k`-decision list the algorithm always finds a useful condition while examples remain (so it
never fails), every output is consistent with the sample, and with
`m ≥ (1/ε)(ln N + ln(1/δ))` examples, `N = 2(2M + 1)^M` for `M = (2n)^k` the number of
conditions (an output uses each condition at most once, so it is one of at most `N` lists), the
probability that some output has error greater than `ε` is at most `δ`; hence `k`-decision
lists are PAC learnable using `k`-decision lists. -/
theorem decision_lists_pac_learnable {n k : ℕ} (hn : 0 < n) (L₀ : DecisionList n k)
    (D : Measure (Cube (Fin n))) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 1 / ε * (Real.log (2 * (2 * (Fintype.card (Condition n k) : ℝ) + 1) ^
      Fintype.card (Condition n k)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalDL L₀) S →
      ∀ (steps : List (Condition n k × Bool)) (R : Finset (Fin m)),
        IsGreedyPrefix S steps R → R.Nonempty → ∃ (c : Condition n k) (b : Bool), IsUseful S R c b) ∧
    (∀ (S : Fin m → Cube (Fin n) × Bool) (L : DecisionList n k),
      IsGreedyOutput S L → IsConsistent (evalDL L) S) ∧
    sampleLaw D (evalDL L₀) m
      {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧ ε < errorOf D (evalDL L₀) (evalDL L)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (decisionListClass n k) (decisionListClass n k) := by sorry

end ComputationalLearning

