import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Assumption 4 ⇒ RE(s, c₀)**, with display **(4.2)**, Bickel–Ritov–Tsybakov,
arXiv:0801.1095v3, Section 4, p. 10. If `1 ≤ s ≤ M`, `c₀ > 0` and `φ_min(s) > 2c₀ θ_{1,1} s`
(Assumption 4), then for every `J0` with `|J0| ≤ s` and every `δ` satisfying (4.1),
`(1/n)|Xδ|₂² ≥ (1/n)δ_{J0}ᵀXᵀXδ_{J0} − 2θ_{1,1}|δ_{J0ᶜ}|₁|δ_{J0}|₁
≥ φ_min(s)|δ_{J0}|₂² − 2c₀θ_{1,1}|δ_{J0}|₁² ≥ (φ_min(s) − 2c₀θ_{1,1}s)|δ_{J0}|₂²`, and RE(s, c₀)
holds with the witness `κ = √(φ_min(s) − 2c₀θ_{1,1}s) > 0`. -/
theorem assumption4_implies_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA4 : 2 * c0 * theta X 1 1 * s < phiMin X s) :
    (∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ≤ gramQuad X δ ∧
      phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2 ≤
        gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ∧
      (phiMin X s - 2 * c0 * theta X 1 1 * s) * l2On δ J0 ^ 2 ≤
        phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2) ∧
    0 < Real.sqrt (phiMin X s - 2 * c0 * theta X 1 1 * s) ∧
    RE X s c0 (Real.sqrt (phiMin X s - 2 * c0 * theta X 1 1 * s)) := by sorry

end LassoDantzig.REConditions
