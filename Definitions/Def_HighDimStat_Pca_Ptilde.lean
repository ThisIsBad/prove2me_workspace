import Mathlib

namespace HighDimStat.Pca

/-- The transformed perturbation vector `p̃ ∈ ℝ^{d-1}` of Wainwright, *High-Dimensional
Statistics* (2019), Eq. (8.11), realized basis-independently as the component of `Pθ*`
orthogonal to `θ*` (equivalently, the off-diagonal block `U₂ᵀPθ*` of `P` transformed into any
orthonormal eigenbasis `U` of `Σ` with first column `θ*` — a quantity that does not depend on
the choice of the remaining `d-1` basis vectors `U₂`). -/
def ptilde {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (θstar : Fin d → ℝ) : Fin d → ℝ :=
  fun j => (P.mulVec θstar) j - (∑ i, (P.mulVec θstar) i * θstar i) * θstar j

end HighDimStat.Pca
