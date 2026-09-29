import Mathlib
import Definitions.Def_BassokSubstitution_Allocation

namespace BassokSubstitution

open MeasureTheory

variable {N : ℕ}

/-- Expected single-period profit, Eq. (2):
`P(x, y) = -∑_k c_k (y_k - x_k) + ∫ G(y, d) dF(d)`, where `x` is the starting inventory,
`y` the inventory after ordering, and `μ` the joint law of the demand vector. -/
noncomputable def Model.profit (M : Model N) (μ : Measure (Fin N → ℝ)) (x y : Fin N → ℝ) : ℝ :=
  -(∑ k, M.c k * (y k - x k)) + ∫ d, M.G y d ∂μ

/-- Standing hypotheses on the marginal demand laws `ν i` (the joint law is the product
`Measure.pi ν`, i.e. independent classes): each demand is nonnegative almost surely, has
finite mean, and has a density (is absolutely continuous w.r.t. Lebesgue measure). -/
def DemandLaw (ν : Fin N → Measure ℝ) : Prop :=
  ∀ i, ν i (Set.Iio 0) = 0 ∧ Integrable id (ν i) ∧ ν i ≪ volume

/-- Every marginal demand law charges every nonempty open interval of `[0, ∞)`:
`ν i (a, b) > 0` whenever `0 ≤ a < b`. -/
def FullSupport (ν : Fin N → Measure ℝ) : Prop :=
  ∀ i (a b : ℝ), 0 ≤ a → a < b → 0 < ν i (Set.Ioo a b)

end BassokSubstitution
