import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Remark 7.1 (p. 662): for jobs `i, j` with intervals `[a, b]` and `[c, d]` and `a ≤ d`,
`p_i ≤ 1/k^⌈b⌉`, `w_j ≤ k^⌈c⌉`; if `i, j` are incomparable then `p_i w_j = 1` or
`p_i w_j ≤ 1/k`; `p_i w_j ≥ k` implies `b < c`; and `p_i w_j = 1` implies `⌈b⌉ = ⌈c⌉`. -/
theorem remark_7_1 {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : left L x ≤ right L y) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ ∧
    weight L k y ≤ k ^ ⌈left L y⌉ ∧
    (Incomparable (prec L) x y →
      procTime L k x * weight L k y = 1 ∨ procTime L k x * weight L k y ≤ 1 / k) ∧
    (k ≤ procTime L k x * weight L k y → right L x < left L y) ∧
    (procTime L k x * weight L k y = 1 → ⌈right L x⌉ = ⌈left L y⌉) := by sorry

end SingleMachinePrec.IntervalReduction

