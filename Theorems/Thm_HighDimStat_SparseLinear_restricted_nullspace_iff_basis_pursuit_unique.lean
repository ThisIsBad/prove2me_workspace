import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty
import Definitions.Def_HighDimStat_SparseLinear_IsBasisPursuitSolution

namespace HighDimStat.SparseLinear

/-- **Theorem 7.8**, Wainwright, *High-Dimensional Statistics* (2019), p. 202. The following two
properties are equivalent: (a) for any vector `θ* ∈ ℝ^d` with support `S`, the basis pursuit
program (7.9) applied with `y = Xθ*` has unique solution `θhat = θ*`; (b) the matrix `X`
satisfies the restricted nullspace property with respect to `S`. -/
theorem restricted_nullspace_iff_basis_pursuit_unique {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (∀ θstar : Fin d → ℝ, HasSupport θstar S →
      ∀ θhat : Fin d → ℝ, IsBasisPursuitSolution X (X.mulVec θstar) θhat → θhat = θstar)
    ↔ RestrictedNullspaceProperty X S := by sorry

end HighDimStat.SparseLinear

