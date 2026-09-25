import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem dualoc_cs_violation {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) (a : Fin n → Fin m) (hPDP : PDP chat f v Jp) (ha : NearestIn chat Jp a)
    (i : Fin n) :
    ViolatesCS chat v Jp a i ↔ 2 ≤ (Jp.filter (fun j => chat i j < v i)).card := by sorry

end SupplyChainTheory
