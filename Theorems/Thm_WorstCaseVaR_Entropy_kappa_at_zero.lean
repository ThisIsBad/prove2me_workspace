import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Remark after Theorem 9, p. 553: for `d = 0`, `f(ε, 0) = ε` and hence
`κ(ε, 0) = -Φ⁻¹(ε)`; and the risk factor `κ(ε, d)` increases with `d ≥ 0`. -/
theorem kappa_at_zero (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    fEntropy ε 0 = ε ∧ kappaEntropy ε 0 = -normalQuantile ε ∧
      StrictMonoOn (kappaEntropy ε) (Set.Ici 0) := by sorry

end WorstCaseVaR.Entropy
