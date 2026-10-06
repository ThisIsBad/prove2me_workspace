import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 2 (p. 1351, Eqs. (11) and (14)): for every period `t ∈ {1, …, T}` and every
fixed vector `o_t`, the smallest minimizer `y_t(o_t)` of `V_t(·, o_t)` exists, and ordering up to it
is optimal: `J_t(x, o_t) = V_t(max(y_t(o_t), x), o_t)` for every `x`. -/
theorem base_stock_optimal {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ y : ℝ, IsLeastMinimizer (fun z => P.V t z o) y ∧
      ∀ x : ℝ, P.J t x o = P.V t (max y x) o := by sorry

end GallegoOzerADI.ZeroSetup

