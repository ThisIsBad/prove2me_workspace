import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

namespace GallegoOzerADI.PositiveSetup

theorem sS_structure (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (hcont : Continuous V) (S : ℝ) (hS : ∀ x, V S ≤ V x)
    (hiii : ∃ x, x < S ∧ K + V S < V x) :
    ∃ s : ℝ, IsGreatest {x | reorderGap K V x ≤ 0} s ∧
      (∀ x, (x < S ∧ orderCost K V x = K + V S) ↔ x ≤ s) ∧
      ∀ x, orderCost K V x = V (max s x) := by sorry

end GallegoOzerADI.PositiveSetup
