import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Assumption 5 ⇒ RE(s, c₀)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Section 4, p. 11,
condition (4.3). If every diagonal entry of `Ψ_n = XᵀX/n` equals 1, `1 ≤ s ≤ M`, `c₀ > 0` and
`θ_{1,1} < 1/((1 + 2c₀)s)`, then for every `J0` with `|J0| ≤ s` and every `δ`,
`δ_{J0}ᵀXᵀXδ_{J0}/n ≥ |δ_{J0}|₂² − θ_{1,1}|δ_{J0}|₁² ≥ |δ_{J0}|₂²(1 − θ_{1,1}s)`, and RE(s, c₀)
holds with the witness `κ = √(1 − (1 + 2c₀)θ_{1,1}s) > 0` (obtained by combining this with (4.2)). -/
theorem assumption5_implies_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hdiag : ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA5 : theta X 1 1 < 1 / ((1 + 2 * c0) * s)) :
    (∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ,
      l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2 ≤ gramQuad X (restrict δ J0) ∧
      l2On δ J0 ^ 2 * (1 - theta X 1 1 * s) ≤ l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2) ∧
    0 < Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s) ∧
    RE X s c0 (Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s)) := by sorry

end LassoDantzig.REConditions
