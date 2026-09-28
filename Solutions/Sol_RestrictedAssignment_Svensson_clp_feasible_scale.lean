import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson

theorem aux_clpscale_configs_eq {J M : Type} [Fintype J] [Fintype M] [DecidableEq J]
    [DecidableEq M] (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (hT : 0 < T) (i : M) :
    configs Γ p T i = configs Γ (fun j => p j / T) 1 i := by
  unfold configs
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_div, div_le_one hT]

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (hT : 0 < T) :
    CLPFeasible Γ p T ↔ CLPFeasible Γ (fun j => p j / T) 1 := by
  unfold CLPFeasible
  simp only [aux_clpscale_configs_eq Γ p T hT]
