import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Proof of Theorem 7, p. 24: for a compact, `μ̄`-strongly convex set `S` with `μ̄ > 0` that is
not a singleton, the only degenerate cost vector is `0`, i.e. `𝒞° = {0}`. -/
theorem degenerate_eq_singleton_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    SPOBounds.Shared.degenerate S = {0} := by sorry

end SPOBounds.StronglyConvex
