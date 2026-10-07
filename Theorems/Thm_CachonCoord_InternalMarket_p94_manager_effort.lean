import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- §6.9.1, p. 94 (Cachon 2003, 3rd draft). Assume `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` is
integrable, `E[Y] > 0`, and `e° > 0` satisfies (45):
`((η − 1)/η)(e°)^{−1/η} K − c'(e°) = 0`. Let the supplier pay the production manager the rate (46)
per unit of realized output, so that his expected utility is `u(e) = payRate(e°) · E[Ye] − c(e)`. Then
1. `u'(e) = ((η − 1)/η)(e°)^{−1/η} K − c'(e)` for every `e > 0`;
2. `e°` is the manager's unique optimal effort over `[0, ∞)`;
3. the supplier earns zero expected profit from the internal market at `e°`:
   `E[Q w(A, Q) | e°] − payRate(e°) · E[Q | e°] = 0`. -/
theorem p94_manager_effort {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P)
    (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo)
    (h45 : (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) :
    (∀ e : ℝ, 0 < e → HasDerivAt (M.managerUtility eo)
      ((M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
    (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
    M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0 := by sorry

end CachonCoord.InternalMarket

