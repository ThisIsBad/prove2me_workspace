import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

/-- Corollary, second clause, corrected (p. 276): `xᵀy = Vex_Ω xᵀy` at every point `(x, y)` of the
box `Ω` whose coordinate pair `(x_i, y_i)` lies on the boundary `∂Ω_i` of its rectangle for
**every** `i`. (As printed, "for all `(x, y) ∈ ∂Ω`", the clause is false for `n ≥ 2`.) -/
theorem vex_bilinear_eq_on_faces {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hface : ∀ i, (z.1 i, z.2 i) ∈ frontier (Ω.rect i)) :
    convexEnvelope Ω.toSet bilin z = bilin z := by sorry

end BiconvexProg.BranchBound
