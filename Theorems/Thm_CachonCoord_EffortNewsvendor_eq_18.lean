import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

/-- Eq. (18), p. 42: if `e°(q) > 0` maximizes the channel profit `e ↦ Π(q, e)` over effort
levels `e ≥ 0`, then `Π(q, ·)` is differentiable at `e°(q)` with derivative
`p ∂S(q, e°(q))/∂e − g′(e°(q))`, where `∂S(q, e)/∂e = −∫_0^q ∂F(y|e)/∂e dy`, and this derivative
is `0`. -/
theorem eq_18 (M : Model) (q eo : ℝ) (hq : 0 ≤ q) (heo : 0 < eo)
    (hmax : IsMaxOn (fun e => M.Pi q e) (Set.Ici 0) eo) :
    HasDerivAt (fun e => M.Pi q e)
        (M.p * (-∫ y in (0 : ℝ)..q, M.effortSlope y eo) - M.effortCost' eo) eo ∧
      M.p * (-∫ y in (0 : ℝ)..q, M.effortSlope y eo) - M.effortCost' eo = 0 := by sorry

end CachonCoord.EffortNewsvendor

