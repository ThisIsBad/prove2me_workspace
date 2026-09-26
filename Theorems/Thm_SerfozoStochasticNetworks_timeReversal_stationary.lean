import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem timeReversal_stationary {E : Type*} (q qbar : E → E → ℝ) (π : E → ℝ)
    (hπ : ∀ x, 0 < π x) (hq : ∀ x, Summable (q x)) (hqbar : ∀ x, Summable (qbar x))
    (hin : ∀ x, Summable fun y => π y * q y x)
    (hrev : ∀ x y, qbar x y = (π x)⁻¹ * π y * q y x)
    (hrate : ∀ x, ∑' y, q x y = ∑' y, qbar x y) :
    IsInvariant q π := by sorry

end SerfozoStochasticNetworks
