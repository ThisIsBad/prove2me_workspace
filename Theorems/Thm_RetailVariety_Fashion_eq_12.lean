import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization
import Definitions.Def_RetailVariety_Fashion_ProofObjects

namespace RetailVariety.Fashion

/-- (12), p. 1506: `∑_{j=1}^r g(v_j) ≤ ∑_{j=1}^r g(w′_j)`, and the same with `g^T`, where
`L = ∑_{j=1}^r v_j + v_0`. Lean's `t` is the paper's `t − 1` and `θ` the paper's `δ`. -/
theorem eq_12 {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j)
    (L : ℝ) (hL : L = ∑ j ∈ RetailVariety.Statics.A n r, v j + v0) :
    ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) ∧
      ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) := by sorry

end RetailVariety.Fashion

