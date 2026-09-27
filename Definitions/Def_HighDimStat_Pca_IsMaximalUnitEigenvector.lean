import Mathlib

namespace HighDimStat.Pca

/-- `θ` is a maximal unit-norm eigenvector of `M`: `θ ∈ S^{d-1}` and `θ` maximizes the Rayleigh
quotient `⟨θ, Mθ⟩` over the whole unit sphere, the variational characterization of the maximal
eigenvector/eigenvalue pair used throughout Wainwright, *High-Dimensional Statistics* (2019),
Eq. (8.14) (`maxθ∈C ⟨θ, Σθ⟩`, specialized here to `C = S^{d-1}`, the case Theorem 8.5 and
Lemma 8.6 both use). The associated top eigenvalue `γ₁(M)` is `⟨θ, Mθ⟩` itself. -/
def IsMaximalUnitEigenvector {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (θ : Fin d → ℝ) : Prop :=
  (∑ j, (θ j) ^ 2 = 1) ∧
  ∀ v : Fin d → ℝ, (∑ j, (v j) ^ 2 = 1) → ∑ i, v i * (M.mulVec v) i ≤ ∑ i, θ i * (M.mulVec θ) i

end HighDimStat.Pca
