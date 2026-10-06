import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 5 (p. 1352): if the myopic levels `y^m_t` (the smallest minimizers of `G_t`) are
nondecreasing in `t ∈ {1, …, T}`, then the myopic policy is optimal: for every period
`t ∈ {1, …, T}` and every (reachable, i.e. nonnegative) vector `o_t` of observed demands, the
optimal base-stock level `y_t(o_t)` of Eq. (11) equals `y^m_t`. -/
theorem myopic_base_stock_optimal {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (ym : ℕ → ℝ) (hym : ∀ t, 1 ≤ t → t ≤ P.T → IsLeastMinimizer (P.G t) (ym t))
    (hmono : MonotoneOn ym (Set.Icc 1 P.T))
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) (ho : 0 ≤ o) :
    IsLeastMinimizer (fun y => P.V t y o) (ym t) := by sorry

end GallegoOzerADI.ZeroSetup

