import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_MM1

open scoped ENNReal

namespace SennottDP.ContinuousTime

/-- Proposition 10.4.1 (p. 250). -/
theorem mm1_serve_avg_cost (lam H a : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hlam : 0 < lam)
    (hrates : ∀ b ∈ rates, 0 < b) (hc : ∀ b ∈ rates, 0 ≤ c b) (hH : 0 < H)
    (ha : a ∈ rates) (hla : lam < a) :
    ∀ i, CTMDC.avgCost (mm1Serve lam rates c (fun k => H * k) a ha) i =
      ENNReal.ofReal (lam / a * c a + H * (lam / a) / (1 - lam / a)) := by sorry

end SennottDP.ContinuousTime

