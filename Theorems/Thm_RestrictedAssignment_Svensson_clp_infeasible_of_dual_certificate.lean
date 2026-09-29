import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 8, proof of Lemma 3.7 (used again on p. 15): a feasible
solution `(y, z)` of the dual of [C-LP] with `∑_i y_i < ∑_j z_j` certifies that [C-LP] is
infeasible. -/
theorem clp_infeasible_of_dual_certificate {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (y : M → ℝ) (z : J → ℝ)
    (hdual : CLPDualFeasible Γ p T y z) (hneg : ∑ i, y i < ∑ j, z j) :
    ¬ CLPFeasible Γ p T := by sorry

end RestrictedAssignment.Svensson
