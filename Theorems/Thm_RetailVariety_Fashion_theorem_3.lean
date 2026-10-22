import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace RetailVariety.Fashion

/-- Theorem 3 (van Ryzin & Mahajan 1999, pp. 1505–1506). Two categories `v`, `w` with the same
`n` variants (sorted decreasingly, nonnegative preferences), the same `p, c, λ, σ, β` and equal
no-purchase preference `v_0 = w_0`. If `A_r` maximizes `π(·, v)`, `A_l` maximizes `π(·, w)` and
`v ≺ w`, then `π(A_r, v) ≤ π(A_l, w)`, for `π = π_I` (7) and for `π = π_T` (8). -/
theorem theorem_3 {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (r l : ℕ) (hr : r ≤ n) (hl : l ≤ n)
    (hvw : Majorized v w) :
    ((∀ S : Finset (Fin n), profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitI p c lam σ β w v0 S ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) →
      profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) ∧
    ((∀ S : Finset (Fin n), profitT p c lam v v0 S ≤ profitT p c lam v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitT p c lam w v0 S ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) →
      profitT p c lam v v0 (RetailVariety.Statics.A n r) ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) := by sorry

end RetailVariety.Fashion

