import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **(A.1)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Appendix A, p. 19. For any partition
`J0ᶜ = J 1 ∪ ⋯ ∪ J K` and `P01` the orthogonal projector in `ℝⁿ` onto the span of the columns
of `X_{J01}`, `J01 = J0 ∪ J 1`:
`|P01 Xδ|₂ ≥ |P01 X δ_{J01}|₂ − |∑_{k=2}^K P01 X δ_{Jk}|₂ = |X δ_{J01}|₂ − |∑_{k=2}^K P01 X δ_{Jk}|₂
≥ |X δ_{J01}|₂ − ∑_{k=2}^K |P01 X δ_{Jk}|₂`. -/
theorem eq_A1_projection_triangle {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hJ : IsBlockPartition J0ᶜ J K) :
    projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ‖∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k))))‖
      ≤ projNorm X (J0 ∪ J 1) (X.mulVec δ) ∧
    projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J0 ∪ J 1))) =
      euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) ∧
    euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ∑ k ∈ Finset.Icc 2 K, projNorm X (J0 ∪ J 1) (X.mulVec (restrict δ (J k)))
      ≤ euclNorm (X.mulVec (restrict δ (J0 ∪ J 1))) -
        ‖∑ k ∈ Finset.Icc 2 K,
          (colSpan X (J0 ∪ J 1)).starProjection (WithLp.toLp 2 (X.mulVec (restrict δ (J k))))‖ := by sorry

end LassoDantzig.REConditions
