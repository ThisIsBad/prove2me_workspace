import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

namespace QueueingFundamentals.Bounds

open MeasureTheory ProbabilityTheory Filter Topology

/-- pp.334–336, Eqs. (7.15)–(7.16). For a stationary G/G/1 queue with `ρ < 1`:
`f(z) = z − ∫_{−z}^{∞} [1 − U(t)] dt` has a unique nonnegative root `r₀`; the stationary line delay
has finite mean with `W_q ≥ f₁(W_q)` (7.16); and for that root, `f₁(z) > z` for `z < r₀` and
`f₁(z) ≤ z` for `z ≥ r₀` (7.15), and `W_q ≥ r₀`. -/
theorem r0_lower_bound
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    (∃! r : ℝ, 0 ≤ r ∧ rootFun A B r = 0) ∧
    Integrable (fun w : ℝ => w) ν ∧
    f1 A B (meanWait ν) ≤ meanWait ν ∧
    ∀ r : ℝ, 0 ≤ r → rootFun A B r = 0 →
      (∀ z : ℝ, (z < r → z < f1 A B z) ∧ (r ≤ z → f1 A B z ≤ z)) ∧ r ≤ meanWait ν := by sorry

end QueueingFundamentals.Bounds

