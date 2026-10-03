import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.22 (Balas §13.8, p. 231): `Π` equals its projection system: `Π = Proj_π{π_j ≤
Σ_{A∋j} u_A for j∈N, Σ_A u_Ar_i(A)≤1 for i=1,2, π≥0, u_A≥0 for all A⊆N}`. -/
theorem pi_projection_characterization {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) :
    PiSet r1 r2 = PiProjSystem r1 r2 := by sorry

end Disjunctive.Polymatroids

