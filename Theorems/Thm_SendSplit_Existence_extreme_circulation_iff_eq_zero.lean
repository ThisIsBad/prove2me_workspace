import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

theorem extreme_circulation_iff_eq_zero {n : ℕ} (G : ArcGraph n) (x : Fin n → Fin n → ℝ)
    (hx : IsCirculation G x) :
    IsExtremeFlow G (fun _ => 0) x ↔ x = 0 := by sorry

end SendSplit.Existence

