import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- Eq. (46), §6.9.1, p. 94 (Cachon 2003, 3rd draft): if `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` is
integrable and `E[Y] > 0`, then for every effort `e° > 0` the per-unit payment
`((η − 1)/η)(e°)^{−1/η} K / E[Y]` equals `E[Q w(A, Q) | e°] / E[Q | e°]` with `Q = Y e°`. -/
theorem eq_46 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P)
    (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.payRate eo = M.expMarketRevenue eo / M.expOutput eo := by sorry

end CachonCoord.InternalMarket

