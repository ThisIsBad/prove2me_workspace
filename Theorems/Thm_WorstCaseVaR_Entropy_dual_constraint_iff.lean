import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- End of the proof of Theorem 9, p. 554: for `d > 0` and `0 < ε < 1`, there is `λ > 0` with
`λd + λ log((e^{1/λ} - 1)φ(γ) + 1) ≤ ε` if and only if `γ ≥ κ(ε, d)√(wᵀΓw) - wᵀx̂`. -/
theorem dual_constraint_iff {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) (γ : ℝ) :
    (∃ lam > 0, dualValue d (gaussianTail xhat Γ w γ) lam ≤ ε) ↔
      kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ w xhat ≤ γ := by sorry

end WorstCaseVaR.Entropy
