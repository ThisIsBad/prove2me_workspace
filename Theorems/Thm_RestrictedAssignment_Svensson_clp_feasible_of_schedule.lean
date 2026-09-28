import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: a schedule respecting `Γ` of makespan at most
`T` defines a feasible solution of [C-LP] with target makespan `T`; hence `OPT_LP ≤ OPT`. -/
theorem clp_feasible_of_schedule {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (σ : J → M) (hσ : ∀ j, σ j ∈ Γ j)
    (hload : ∀ i, schedLoad p σ i ≤ T) :
    CLPFeasible Γ p T := by sorry

end RestrictedAssignment.Svensson
