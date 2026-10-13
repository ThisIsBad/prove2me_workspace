import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Claim 2 (p. 663): an incomparable pair of jobs `(i, j)` has `p_i w_j = 1` if `(i, j) ∈ D`,
and `p_i w_j ≤ 1/k` otherwise. -/
theorem claim_2 {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : Incomparable (prec L) x y) :
    (InD L x y → procTime L k x * weight L k y = 1) ∧
    (¬ InD L x y → procTime L k x * weight L k y ≤ 1 / k) := by sorry

end SingleMachinePrec.IntervalReduction

