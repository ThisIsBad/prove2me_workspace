import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d
import Definitions.Def_OnlinePrimalDual_MTS_costStandard
import Definitions.Def_OnlinePrimalDual_MTS_costNewPhases

namespace OnlinePrimalDual.MTS

theorem aux_nts_termwise {V : Type*} {k : ℕ} (ws : WeightedStar V)
    (s : Fin k → V) (w : Fin k → ℝ) (hw_le : ∀ i, w i ≤ ws.d (s i)) :
    ∑ i, (w i + ws.d (s i)) ≤ ∑ i, 2 * ws.d (s i) := by
  apply Finset.sum_le_sum
  intro i _
  have := hw_le i
  linarith

end OnlinePrimalDual.MTS

open OnlinePrimalDual.MTS

theorem solution {V : Type*} {k : ℕ} (ws : WeightedStar V)
    (s : Fin k → V) (w : Fin k → ℝ) (hw_le : ∀ i, w i ≤ ws.d (s i)) :
    costStandard ws s w ≤ 2 * costNewPhases ws s := by
  unfold costStandard costNewPhases
  rw [Finset.mul_sum]
  exact aux_nts_termwise ws s w hw_le
