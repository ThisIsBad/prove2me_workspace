import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: if [C-LP] is feasible for target makespan `T₀`
then it is feasible for every `T ≥ T₀`. -/
theorem clp_feasible_mono {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T0 T : ℝ) (hT : T0 ≤ T) (h : CLPFeasible Γ p T0) :
    CLPFeasible Γ p T := by sorry

end RestrictedAssignment.Svensson
