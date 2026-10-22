import Mathlib
import Definitions.Def_WhittEfficiency_MMs_WaitLaw

open MeasureTheory ProbabilityTheory

namespace WhittEfficiency.MMs

/-- Whitt (1992), §3.1, p. 719: conditional on a positive wait, the M/M/s wait
is exponential with mean `1 / (s * (1 - ρ))`. -/
theorem sec_3_1_conditional_exponential
    (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (waitLaw s p).restrict (Set.Ioi (0 : ℝ)) =
        (waitLaw s p) (Set.Ioi (0 : ℝ)) •
          expMeasure ((s : ℝ) * (1 - lam / (s : ℝ))) := by sorry

end WhittEfficiency.MMs

