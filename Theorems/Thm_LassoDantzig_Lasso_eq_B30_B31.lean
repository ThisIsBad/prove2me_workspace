import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.30)–(B.31), p. 28 (proof of Theorem 7.2): for `r > 0`, on the noise event `𝒜`, for `y = Xβ* + w`
with unit diagonal, `𝓜(β*) ≤ s` and Assumption RE(s, 3) with witness `κ`, every Lasso solution
`β̂` satisfies, with `δ = β̂ − β*` and `J₀ = J(β*)`,
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2` (B.30), the cone condition (4.1) with `c₀ = 3`, and
`(1/n)|Xδ|_2² ≤ 16 r² s / κ²`, `|δ_{J₀}|_2 ≤ 4r√s / κ²` (B.31). -/
theorem eq_B30_B31 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 3 κ)
    (r : ℝ) (hr : 0 < r) (w : Fin n → ℝ) (hw : NoiseEventHalf X r w)
    (βhat : Fin M → ℝ) (hL : IsLasso X (fun i => X.mulVec βstar i + w i) r βhat) :
    (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤
        4 * r * Real.sqrt s * l2On (βhat - βstar) (supp βstar) ∧
      ConeCond 3 (supp βstar) (βhat - βstar) ∧
      (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤ 16 * r ^ 2 * s / κ ^ 2 ∧
      l2On (βhat - βstar) (supp βstar) ≤ 4 * r * Real.sqrt s / κ ^ 2 := by sorry

end LassoDantzig.Lasso
