import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- The Candès–Tao bound used in the proof of **Lemma 4.1 (i)**, Bickel–Ritov–Tsybakov,
arXiv:0801.1095v3, Appendix A, p. 20 (display after (A.3), "cf. [7]"). If `J` and `J'` are
disjoint, `|J| ≤ s`, `|J'| ≤ 2s` and `φ_min(2s) > 0`, then for the orthogonal projector
`P_{J'}` onto the span of the columns of `X_{J'}`:
`(1/√n)|P_{J'} X δ_J|₂ ≤ (θ_{s,2s}/√φ_min(2s)) |δ_J|₂`. In the proof `J = J_k` (`k ≥ 2`) and
`J' = J01`. -/
theorem candes_tao_correlation_bound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (s : ℕ) (hs : 1 ≤ s)
    (δ : Fin M → ℝ) (J J' : Finset (Fin M)) (hdisj : Disjoint J J')
    (hJ : J.card ≤ s) (hJ' : J'.card ≤ 2 * s) (hφ : 0 < phiMin X (2 * s)) :
    1 / Real.sqrt n * projNorm X J' (X.mulVec (restrict δ J)) ≤
      theta X s (2 * s) / Real.sqrt (phiMin X (2 * s)) * l2On δ J := by sorry

end LassoDantzig.REConditions
