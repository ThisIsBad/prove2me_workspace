import Mathlib
import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem second_price_dominant {m : ℕ} (v b : ℝ) (others : Fin m → ℝ) :
    spSurplus v b others ≤ spSurplus v v others := by sorry

end RevenueManagement
