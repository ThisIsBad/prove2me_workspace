import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Theorem 7, first claim, p. 23: for a compact, `μ̄`-strongly convex set `S` with `μ̄ > 0`
that is not a singleton, the distance to degeneracy is the dual norm: `ν_S(ĉ) = ‖ĉ‖_*` for
every cost vector `ĉ`. -/
theorem nu_eq_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    ∀ chat : StrongDual ℝ E, SPOBounds.Shared.nu S chat = ‖chat‖ := by sorry

end SPOBounds.StronglyConvex
