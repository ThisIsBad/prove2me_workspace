import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 1 (p. 1351): for every period `t ∈ {1, …, T}` and every fixed vector `o_t`,
`V_t(·, o_t)` is convex and `V_t(x, o_t) → ∞` as `|x| → ∞`. -/
theorem V_convex_coercive {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ConvexOn ℝ Set.univ (fun x => P.V t x o) ∧
      Tendsto (fun x => P.V t x o) (cocompact ℝ) atTop := by sorry

end GallegoOzerADI.ZeroSetup

