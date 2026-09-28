import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: scaling the processing times by `1/T` turns
[C-LP] for target makespan `T > 0` into [C-LP] for target makespan 1. -/
theorem clp_feasible_scale {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (hT : 0 < T) :
    CLPFeasible Γ p T ↔ CLPFeasible Γ (fun j => p j / T) 1 := by sorry

end RestrictedAssignment.Svensson
