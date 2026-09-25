import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem dualoc_gap {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) (a : Fin n → Fin m) (hPDP : PDP chat f v Jp) (ha : NearestIn chat Jp a) :
    (∑ j ∈ Jp, f j + ∑ i, chat i (a i)) - ∑ i, v i
      = ∑ i, ∑ j ∈ Jp.erase (a i), max 0 (v i - chat i j) := by sorry

end SupplyChainTheory
