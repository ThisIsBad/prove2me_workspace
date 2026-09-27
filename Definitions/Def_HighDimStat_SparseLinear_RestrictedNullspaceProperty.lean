import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_ConeSet

namespace HighDimStat.SparseLinear

/-- **Definition 7.7.** The matrix `X` satisfies the restricted nullspace property with respect
to `S` if `C(S) ∩ null(X) = {0}`, Wainwright, *High-Dimensional Statistics* (2019), p. 202.
Here `C(S) = ConeSet S 1` and `null(X) = {Δ | X.mulVec Δ = 0}`. -/
def RestrictedNullspaceProperty {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Prop :=
  ∀ Δ : Fin d → ℝ, ConeSet S 1 Δ → X.mulVec Δ = 0 → Δ = 0

end HighDimStat.SparseLinear
