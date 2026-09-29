import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem myopic_bounds {L M : ℕ} [NeZero M] (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (ν : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G) (hK : ∀ t, P.K t = K)
    (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = ν) (t : ℕ) (ht₁ : 1 ≤ t) (htT : t ≤ P.T)
    (o : Fin M → ℝ) (ho : ∀ j, 0 ≤ o j) (S s : ℝ)
    (hS : IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S)
    (hs : IsGreatest {x | P.H t x o ≤ 0} s) :
    myopicOrderUpTo G ≤ S ∧ S ≤ myopicUpperLevel G K α ∧ myopicReorderPoint G K ≤ s := by sorry

end GallegoOzerADI.PositiveSetup
