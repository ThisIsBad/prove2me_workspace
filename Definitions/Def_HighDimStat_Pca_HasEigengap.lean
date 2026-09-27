import Mathlib

namespace HighDimStat.Pca

/-- `M` has eigengap `ν > 0` at its maximal eigenvector `θ*`: every unit vector orthogonal to
`θ*` has Rayleigh quotient at most `γ₁(M) − ν`, the variational (Courant–Fischer) form of
Wainwright's `ν := γ₁(Σ) − γ₂(Σ) > 0`, Section 8.2.1, p. 242, used in Theorem 8.5 and
Lemma 8.6. -/
def HasEigengap {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (θstar : Fin d → ℝ) (ν : ℝ) : Prop :=
  0 < ν ∧
  ∀ v : Fin d → ℝ, (∑ j, (v j) ^ 2 = 1) → (∑ j, v j * θstar j = 0) →
    ∑ i, v i * (M.mulVec v) i ≤ (∑ i, θstar i * (M.mulVec θstar) i) - ν

end HighDimStat.Pca
