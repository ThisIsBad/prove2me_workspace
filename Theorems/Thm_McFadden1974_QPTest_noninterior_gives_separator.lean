import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false

namespace McFadden1974.QPTest

/-- McFadden (1974), p. 117 (PDF 13), Lemma 4, proof, final paragraph.
Failure of interiority gives a nonzero separating normal, so Axiom 6 fails.
The cone uses every ordered index triple in equation (22). -/
theorem noninterior_gives_separator {N K : ℕ} (d : ChoiceData N K)
    (h : (0 : EuclideanSpace ℝ (Fin K)) ∉ interior d.coneSet) :
    (∃ γ : EuclideanSpace ℝ (Fin K), γ ≠ 0 ∧
      ∀ n i j, inner ℝ (d.w n i j) γ ≤ 0) ∧ ¬ d.Axiom6 := by sorry

end McFadden1974.QPTest

