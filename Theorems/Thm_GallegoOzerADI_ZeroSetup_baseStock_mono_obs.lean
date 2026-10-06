import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 5 (p. 1351): for every period `t ∈ {1, …, T}`, the base-stock level `y_t(o_t)`
(the smallest minimizer of `V_t(·, o_t)`, Eq. (11)) is increasing (nondecreasing) in `o_t` for the
componentwise order. -/
theorem baseStock_mono_obs {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o o' : Fin M → ℝ) (y y' : ℝ)
    (hoo : o ≤ o') (hy : IsLeastMinimizer (fun z => P.V t z o) y)
    (hy' : IsLeastMinimizer (fun z => P.V t z o') y') :
    y ≤ y' := by sorry

end GallegoOzerADI.ZeroSetup

