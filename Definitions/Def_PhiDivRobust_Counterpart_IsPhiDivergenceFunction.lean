import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- A φ-divergence function (Ben-Tal et al. 2013, p. 343, the sentence after Eq. (2); Table 2 note and
footnote 2, p. 344). `φ : ℝ → EReal` is never `-∞`, is finite on `(0, ∞)`, satisfies `φ(1) = 0`, and is
convex on `[0, ∞)` (convexity written out in `EReal`, since `ConvexOn` needs a module codomain).
The value `φ 0` may be `+∞` (Burg, χ², J divergences); values at `t < 0` are unconstrained and never
used. -/
structure IsPhiDivergenceFunction (φ : ℝ → EReal) : Prop where
  ne_bot : ∀ t, φ t ≠ ⊥
  ne_top_of_pos : ∀ t, 0 < t → φ t ≠ ⊤
  map_one : φ 1 = 0
  convex : ∀ t u θ : ℝ, 0 ≤ t → 0 ≤ u → 0 ≤ θ → θ ≤ 1 →
    φ (θ * t + (1 - θ) * u) ≤ (θ : EReal) * φ t + ((1 - θ : ℝ) : EReal) * φ u

end PhiDivRobust.Counterpart
