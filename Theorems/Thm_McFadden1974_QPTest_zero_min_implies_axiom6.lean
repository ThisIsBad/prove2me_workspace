import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false

namespace McFadden1974.QPTest

/-- McFadden (1974), p. 117 (PDF 13), Lemma 4, proof, first paragraph.
With Axiom 5, an attained zero value in (22) implies Axiom 6. Positivity of
each trial's repetition count is part of `ChoiceData`, as on p. 114. -/
theorem zero_min_implies_axiom6 {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) (h0 : (0 : EuclideanSpace ℝ (Fin K)) ∈ d.qpFeasible) :
    d.Axiom6 := by sorry

end McFadden1974.QPTest

