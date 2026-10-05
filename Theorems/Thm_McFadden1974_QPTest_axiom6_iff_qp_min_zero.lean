import Definitions.Def_McFadden1974_QPTest_ChoiceData

set_option autoImplicit false

namespace McFadden1974.QPTest

/-- McFadden (1974), p. 117 (PDF 13), Lemma 4 and equation (22).
Under Axiom 5, Axiom 6 holds exactly when the quadratic program attains a
minimum of zero. `IsLeast` retains attainment, unlike an infimum equation.
The finite data model includes at least two alternatives and at least one
observed choice per trial; Axiom 5 uses the equivalent difference span form. -/
theorem axiom6_iff_qp_min_zero {N K : ℕ} (d : ChoiceData N K)
    (h5 : d.Axiom5) :
    d.Axiom6 ↔
      IsLeast ((fun y : EuclideanSpace ℝ (Fin K) => ‖y‖ ^ 2) '' d.qpFeasible) 0 := by sorry

end McFadden1974.QPTest

