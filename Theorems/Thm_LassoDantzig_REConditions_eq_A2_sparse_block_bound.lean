import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **(A.2)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Appendix A, p. 19. If `|J| ≤ m` (so
`δ_J` has at most `m` non-zero components), then for the orthogonal projector `P_{J'}` onto the
span of the columns of `X_{J'}` (any `J'`, in particular `J' = J01`):
`(1/√n)|P_{J'} X δ_J|₂ ≤ (1/√n)|X δ_J|₂ ≤ √φ_max(m) |δ_J|₂`. -/
theorem eq_A2_sparse_block_bound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (m : ℕ) (hm : 1 ≤ m)
    (δ : Fin M → ℝ) (J J' : Finset (Fin M)) (hJ : J.card ≤ m) :
    1 / Real.sqrt n * projNorm X J' (X.mulVec (restrict δ J)) ≤
        1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ J)) ∧
    1 / Real.sqrt n * euclNorm (X.mulVec (restrict δ J)) ≤
        Real.sqrt (phiMax X m) * l2On δ J := by sorry

end LassoDantzig.REConditions
