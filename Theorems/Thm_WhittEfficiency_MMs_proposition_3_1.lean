import Mathlib
import Definitions.Def_WhittEfficiency_MMs_WaitLaw

open MeasureTheory ProbabilityTheory

namespace WhittEfficiency.MMs

/-- Whitt (1992), Proposition 3.1, p. 720, (16)–(17), with the printed omissions
corrected: the exponent in (16) includes `x`, and the denominator in (17) is `γ√s`. -/
theorem proposition_3_1
    (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p)
    (γ : ℝ) (h1 : (1 - lam / (s : ℝ)) * Real.sqrt s = γ) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x →
        (waitLaw s p).real (Set.Ioi x) /
          (waitLaw s p).real (Set.Ioi (0 : ℝ)) =
            Real.exp (-(γ * Real.sqrt s * x))) ∧
      (∫ w in Set.Ioi (0 : ℝ), w ∂(waitLaw s p)) /
        (waitLaw s p).real (Set.Ioi (0 : ℝ)) = 1 / (γ * Real.sqrt s) := by sorry

end WhittEfficiency.MMs

