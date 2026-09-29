import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open Filter Topology

namespace GallegoOzerADI.PositiveSetup

theorem J_abConvex_limits {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ABConvex 0 (P.K t) (fun x => P.J t x o) ∧
      Tendsto (fun x => P.J t x o) atTop atTop ∧
      ∃ s : ℝ, IsGreatest {x | P.H t x o ≤ 0} s ∧
        Tendsto (fun x => P.J t x o) atBot (𝓝 (P.V t s o)) := by sorry

end GallegoOzerADI.PositiveSetup
