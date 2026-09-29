import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 15, Lemma 4.6: if [C-LP] is feasible (target makespan 1),
then in every iteration of Algorithm 2 there is a potential move to pick. -/
theorem exists_potential_move {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hLP : CLPFeasible Γ p 1)
    (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none)
    (s : AlgState J M) (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none) :
    ∃ j i, IsPotentialMove Γ p s j i := by sorry

end RestrictedAssignment.Svensson
