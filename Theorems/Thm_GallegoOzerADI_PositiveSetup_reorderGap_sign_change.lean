import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

namespace GallegoOzerADI.PositiveSetup

theorem reorderGap_sign_change (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (S : ℝ) (hS : ∀ x, V S ≤ V x) (hiii : ∃ x, x < S ∧ K + V S < V x) :
    (∃ x, reorderGap K V x < 0) ∧ (∃ x, 0 < reorderGap K V x) ∧
      ∀ x₁ x₂, x₁ < x₂ → 0 < reorderGap K V x₁ → 0 ≤ reorderGap K V x₂ := by sorry

end GallegoOzerADI.PositiveSetup
