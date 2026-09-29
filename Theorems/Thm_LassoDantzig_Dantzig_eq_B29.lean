import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.29) and the two displays before it (p. 28), deterministic form.
Let `κ > 0` be a witness of RE(s, m, 1), `m ≥ 1`, `|J₀| ≤ s`, `δ` satisfy the cone condition
(4.1) at `J₀` with `c₀ = 1`, `J₁` be a set of the `m` largest `|δⱼ|` outside `J₀`, `r ≥ 0`, and
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2` (the conclusion of (B.25)). Then
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀₁}|_2`, `|δ_{J₀₁}|_2 ≤ 4r√s/κ²`, and
`|δ|_2² ≤ 16 (1 + √(s/m))² (r√s/κ²)²`. -/
theorem eq_B29 {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (hRE : REm X s m 1 κ)
    (J0 J1 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ)
    (hJ1 : IsTopBlock δ J0 J1 m) (r : ℝ) (hr : 0 ≤ r)
    (hB25 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ (J0 ∪ J1) ∧
    l2On δ (J0 ∪ J1) ≤ 4 * r * Real.sqrt s / κ ^ 2 ∧
    ∑ j, δ j ^ 2 ≤
      16 * (1 + Real.sqrt ((s : ℝ) / m)) ^ 2 * (r * Real.sqrt s / κ ^ 2) ^ 2 := by sorry

end LassoDantzig.Dantzig
