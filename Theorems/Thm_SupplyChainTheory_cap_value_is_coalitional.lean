import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem cap_value_is_coalitional {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) :
    IsCoalitionalValue (capValue v) := by sorry

end SupplyChainTheory
