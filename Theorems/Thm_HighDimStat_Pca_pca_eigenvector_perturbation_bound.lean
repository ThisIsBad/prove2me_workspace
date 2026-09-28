import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_OpNormSymm
import Definitions.Def_HighDimStat_Pca_Ptilde
import Definitions.Def_HighDimStat_Pca_L2Norm

namespace HighDimStat.Pca

/-- **Theorem 8.5**, Wainwright, *High-Dimensional Statistics* (2019), Eq. (8.12), p. 243.
Consider a positive semidefinite, symmetric matrix `M` with maximum unit eigenvector `θ*` and
eigengap `ν = γ₁(M) − γ₂(M) > 0`. Given any symmetric matrix `P` with `|||P|||₂ < ν/2`, and
`θ̂` a maximal unit eigenvector of the perturbed matrix `M̂ := M + P` with sign resolved so
that `⟨θ̂,θ*⟩ ≥ 0`, then `‖θ̂ − θ*‖₂ ≤ 2‖p̃‖₂ / (ν − 2|||P|||₂)`. -/
theorem pca_eigenvector_perturbation_bound {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hMsym : M.transpose = M)
    (hMpsd : ∀ v : Fin d → ℝ, 0 ≤ ∑ i, v i * (M.mulVec v) i)
    (hPsym : P.transpose = P)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hPop : opNormSymm P < ν / 2)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat)
    (hsign : 0 ≤ ∑ j, θhat j * θstar j) :
    l2Norm (fun j => θhat j - θstar j) ≤
      (2 * l2Norm (ptilde P θstar)) / (ν - 2 * opNormSymm P) := by sorry

end HighDimStat.Pca

