import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

/-- Proposition 1 (Vial 1983, Prop. 2.9), p. 23, eq. (8): for a `μ̄`-strongly convex set `S`
with `μ̄ ≥ 0` and any `w̄ ∈ S`,
`N_S(w̄) = {c : cᵀ(w − w̄) ≤ −(μ̄/2) ‖c‖_* ‖w − w̄‖² for all w ∈ S}`. -/
theorem normalCone_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {μbar : ℝ} (hμ : 0 ≤ μbar) {S : Set E}
    (hSsc : StronglyConvexSet μbar S) {wbar : E} (hwbar : wbar ∈ S) :
    normalCone S wbar =
      {c : StrongDual ℝ E | ∀ v ∈ S, c (v - wbar) ≤ -(μbar / 2) * ‖c‖ * ‖v - wbar‖ ^ 2} := by sorry

end SPOBounds.StronglyConvex
