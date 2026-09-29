import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Theorem 7, strength claim, p. 23: if the compact set `S` is not a singleton and is
`μ̄`-strongly convex for some `μ̄ > 0`, then for every optimization oracle `w`
(`w ĉ ∈ S` minimizes `v ↦ ĉ v` over `S`) the strength property (5) holds with `μ = μ̄`. -/
theorem strength_property {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ v ∈ S, c (w c) ≤ c v) :
    SPOBounds.Shared.StrengthProperty S μbar w := by sorry

end SPOBounds.StronglyConvex
