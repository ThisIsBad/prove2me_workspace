import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2
import Definitions.Def_JohnsonApprox_ExactCover_LowerBoundInput

namespace JohnsonApprox.ExactCover

/-- Theorem 6, lower bound (p. 271): on the Fig. 1 input with every set of `F₁` filled out from
segment `k` to exactly `k` elements, C2 may choose a subcover of measure at least
`(Σ_{j=1}^k 1/j) · F*`. -/
theorem lowerBound_example (k : ℕ) (hk : 1 ≤ k) :
    (∀ i, ((lbInput k).S i).card = k) ∧ InEC k (lbInput k) ∧ 0 < (lbInput k).opt ∧
      ∃ M, Choosable (lbInput k) M ∧
        (harmonic k : ℝ) * (lbInput k).opt ≤ (lbInput k).measure M := by sorry

end JohnsonApprox.ExactCover

