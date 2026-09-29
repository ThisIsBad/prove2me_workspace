import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open Filter

namespace GallegoOzerADI.PositiveSetup

theorem V_abConvex_coercive {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ABConvex 0 (P.K t) (fun y => P.V t y o) ∧
      Tendsto (fun y => P.V t y o) (cocompact ℝ) atTop := by sorry

end GallegoOzerADI.PositiveSetup
