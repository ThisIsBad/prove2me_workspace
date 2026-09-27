import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_PsiPCA

namespace HighDimStat.Pca

/-- **Lemma 8.6** (PCA basic inequality), Wainwright, *High-Dimensional Statistics* (2019),
Eq. (8.15), p. 243. Given a matrix `M` with eigengap `ν > 0` at its maximal unit eigenvector
`θ*`, and `θ̂` a maximal unit eigenvector of the perturbed matrix `M̂ = M + P`, the error
`Δ = θ̂ − θ*` is bounded as `ν(1 − ⟨θ̂,θ*⟩²) ≤ |Ψ(Δ; P)|`. -/
theorem pca_basic_inequality {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat) :
    ν * (1 - (∑ j, θhat j * θstar j) ^ 2) ≤
      |psiPCA P θstar (fun j => θhat j - θstar j)| := by sorry

end HighDimStat.Pca

