import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_ConeSet

namespace HighDimStat.SparseLinear

/-- **Definition 7.12.** The matrix `X` satisfies the restricted eigenvalue (RE) condition over
`S` with parameters `(κ, α)` if `(1/n)‖XΔ‖₂² ≥ κ‖Δ‖₂²` for all `Δ ∈ C_α(S)`, Wainwright,
*High-Dimensional Statistics* (2019), Eq. (7.22), p. 208. -/
def RestrictedEigenvalue {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (κ α : ℝ) : Prop :=
  ∀ Δ : Fin d → ℝ, ConeSet S α Δ →
    κ * (∑ j, (Δ j) ^ 2) ≤ (∑ i, (X.mulVec Δ i) ^ 2) / (n : ℝ)

end HighDimStat.SparseLinear
