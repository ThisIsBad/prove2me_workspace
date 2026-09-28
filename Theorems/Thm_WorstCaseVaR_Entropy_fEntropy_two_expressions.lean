import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Eq. (45), p. 553: the two expressions of `f(ε, d)` agree,
`sup_{λ>0} (e^{ε/λ-d} - 1)/(e^{1/λ} - 1) = sup_{v>0} (e^{-d}(v + 1)^ε - 1)/v`. -/
theorem fEntropy_two_expressions (ε d : ℝ) :
    fEntropy ε d =
      sSup ((fun v : ℝ => (Real.exp (-d) * (v + 1) ^ ε - 1) / v) '' Set.Ioi 0) := by sorry

end WorstCaseVaR.Entropy
