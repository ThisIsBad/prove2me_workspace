import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, (B.25) (p. 27). Linear model `y = Xβ* + w` with unit diagonal
`XᵀX/n`, `𝓜(β*) ≤ s`, a realised noise vector `w` in the event `ℬ`, and a Dantzig selector
`β̂_D` (7.3). With `δ = β̂_D − β*` and `J₀ = J(β*)`: `β* ∈ Λ`;
(i) `(1/n)|XᵀXδ|_∞ ≤ 2r`; (ii) the cone condition (4.1) holds with `c₀ = 1`; and
`(1/n)|Xδ|_2² ≤ 4r√s |δ_{J₀}|_2`. -/
theorem eq_B25 {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (hdiag : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (βstar : Fin M → ℝ) (s : ℕ) (hsparse : sparsity βstar ≤ s)
    (w : Fin n → ℝ) (r : ℝ) (hB : NoiseEvent X r w)
    (βD : Fin M → ℝ) (hD : IsDantzig X (fun i => X.mulVec βstar i + w i) r βD) :
    InLambda X (fun i => X.mulVec βstar i + w i) r βstar ∧
    (∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βD - βstar) i| ≤ 2 * r) ∧
    ConeCond 1 (supp βstar) (βD - βstar) ∧
    (1 / (n : ℝ)) * ∑ i, X.mulVec (βD - βstar) i ^ 2 ≤
      4 * r * Real.sqrt s * l2On (βD - βstar) (supp βstar) := by sorry

end LassoDantzig.Dantzig
