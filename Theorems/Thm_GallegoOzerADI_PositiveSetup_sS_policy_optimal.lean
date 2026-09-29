import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

namespace GallegoOzerADI.PositiveSetup

theorem sS_policy_optimal {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ S s : ℝ, IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S ∧
      IsGreatest {x | P.H t x o ≤ 0} s ∧
      ∀ x, (x ≤ s → x < S ∧ P.J t x o = P.K t + P.V t S o) ∧
        (s < x → P.J t x o = P.V t x o) := by sorry

end GallegoOzerADI.PositiveSetup
