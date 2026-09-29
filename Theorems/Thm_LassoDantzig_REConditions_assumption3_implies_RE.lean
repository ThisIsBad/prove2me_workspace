import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **Assumption 3 ⇒ RE(s, c₀)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Section 4, p. 10.
If `1 ≤ s ≤ M`, `c₀ > 0` and `φ_min(s) > 2c₀ θ_{s,1} √s` (Assumption 3), then RE(s, c₀) holds
with the explicit witness `κ = √(φ_min(s) − 2c₀ θ_{s,1} √s) > 0` given by the displayed argument. -/
theorem assumption3_implies_RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA3 : 2 * c0 * theta X s 1 * Real.sqrt s < phiMin X s) :
    0 < Real.sqrt (phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s) ∧
    RE X s c0 (Real.sqrt (phiMin X s - 2 * c0 * theta X s 1 * Real.sqrt s)) := by sorry

end LassoDantzig.REConditions
