import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false

namespace McFadden1974.QPTest

/-- McFadden (1974), p. 117 (PDF 13), Lemma 4, proof, second paragraph.
If zero is interior to the generated cone, a strictly positive coefficient
exists for every ordered index triple, yielding zero; rescaling those
coefficients gives a feasible zero of (22). The paper's abbreviated sum is
read with the `i,j` sums present, as required by equation (22). -/
theorem interior_gives_positive_coefficients {N K : ℕ} (d : ChoiceData N K)
    (h : (0 : EuclideanSpace ℝ (Fin K)) ∈ interior d.coneSet) :
    (∃ α : (n : Fin N) → Fin (d.J n) → Fin (d.J n) → ℝ,
      (∀ n i j, 0 < α n i j) ∧
        (∑ n, ∑ i, ∑ j, α n i j • d.w n i j) = 0) ∧
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by sorry

end McFadden1974.QPTest

