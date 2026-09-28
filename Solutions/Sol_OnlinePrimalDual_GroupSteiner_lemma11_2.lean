import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_expectedCost

namespace OnlinePrimalDual.GroupSteiner

theorem aux_l112_eq {E : Type*} [Fintype E] [DecidableEq E] (ρ : RandomCover E) (c : E → ℝ) :
    ρ.expectedCost c = ∑ e, c e * ρ.marg e := by
  unfold RandomCover.expectedCost RandomCover.marg
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  calc ∑ C, ∑ e ∈ C, ρ.p C * c e
      = ∑ C : Finset E, ∑ e : E, if e ∈ C then ρ.p C * c e else 0 := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext e
        simp
    _ = ∑ e : E, ∑ C : Finset E, if e ∈ C then ρ.p C * c e else 0 := Finset.sum_comm
    _ = ∑ e : E, ∑ C : Finset E, if e ∈ C then c e * ρ.p C else 0 := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun C _ => ?_
        split_ifs <;> ring

end OnlinePrimalDual.GroupSteiner

open OnlinePrimalDual.GroupSteiner

theorem solution {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E) (ρ : RandomCover E)
    (w' : E → ℝ) (hmarg : ∀ e, ρ.marg e = w' e) :
    ρ.expectedCost tr.cost ≤ ∑ e, tr.cost e * w' e := by
  rw [aux_l112_eq]
  simp only [hmarg, le_refl]
