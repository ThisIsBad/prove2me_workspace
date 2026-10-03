import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.5, p. 204: if the distribution of `Y` (on `{1, 2, …}`) has
bounded mean residual lifetimes, then `Y` has finite moments of all orders. -/
theorem bmrl_finite_moments (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (hbmrl : IsBMRLDist u) :
    ∀ k : ℕ, moment u k < ∞ := by sorry

end SennottDP.ResidualLife
