import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, p. 93: reducing every multiplicity modulo two preserves parity and cannot raise cost. -/
theorem exists_zero_one_parity_solution_le
    {V E : Type*} [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (x : E → ℕ) (hx : IsParitySolution G x) :
    ∃ x' : E → ℕ, IsParitySolution G x' ∧
      (∀ e, x' e ≤ 1) ∧ cost c x' ≤ cost c x := by sorry
end ChinesePostman.Matching

