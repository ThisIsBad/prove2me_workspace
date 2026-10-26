import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 3 (p. 1351): for every period `t ∈ {1, …, T}` and every fixed vector `o_t`,
`J_t(·, o_t)` is an increasing (nondecreasing) convex function. -/
theorem J_monotone_convex {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    Monotone (fun x => P.J t x o) ∧ ConvexOn ℝ Set.univ (fun x => P.J t x o) := by sorry

end GallegoOzerADI.ZeroSetup

