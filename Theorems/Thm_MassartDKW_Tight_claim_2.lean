import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem claim_2 (n : ℕ) (hn : 1 ≤ n) (ε s' : ℝ) (hε : 0 < ε) (hs' : 0 < s')
    (hnε : 2 ≤ (n : ℝ) * ε) (hns' : 1 ≤ (n : ℝ) * s') (hx : ε ≤ 3 * s') :
    (1 + 2 * ε / (3 * s')) ^ (-(1 / 2 : ℝ)) ≤
      (1 - ε / (3 * s') + ε ^ 2 / (6 * s' ^ 2)) * Real.exp (-(ε ^ 2 * v n s') / (24 * (n : ℝ))) := by sorry

end MassartDKW.Tight

