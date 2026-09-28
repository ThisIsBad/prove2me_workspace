import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.26) (p. 27), deterministic form. If `κ > 0` is a witness of
RE(s, 1), `|J₀| ≤ s`, `δ` satisfies the cone condition (4.1) at `J₀` with `c₀ = 1`, `r ≥ 0`,
and `(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2` (the conclusion of (B.25)), then
`(1/n)|Xδ|_2² ≤ 16r²s/κ²` and `|δ_{J₀}|_2 ≤ 4r√s/κ²`. -/
theorem eq_B26 {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s : ℕ) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ)
    (r : ℝ) (hr : 0 ≤ r)
    (hB25 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 16 * r ^ 2 * s / κ ^ 2 ∧
    l2On δ J0 ≤ 4 * r * Real.sqrt s / κ ^ 2 := by sorry

end LassoDantzig.Dantzig
