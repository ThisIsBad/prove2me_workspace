import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR

namespace NestedLogitVariants.General

/-- Appendix A.4 (p. 46): an optimal solution `(x̂, ŷ)` of (4) with the candidate collections
`{N^k_ij} ∪ {{j}}` has `x̂ ≥ 0`. -/
theorem xh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh) :
    0 ≤ xh := by sorry

end NestedLogitVariants.General

