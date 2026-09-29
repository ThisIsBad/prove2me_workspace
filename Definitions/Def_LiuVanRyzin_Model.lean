import Mathlib

namespace LiuVanRyzin

/-- The customer utility of Liu–van Ryzin (2008), §2, p. 1120: time invariant, strictly
increasing and concave, twice differentiable, with `u 0 = 0`. Customers only evaluate `u` at
nonnegative arguments, so monotonicity, concavity and continuity are imposed on `[0, ∞)` and
twice differentiability on `(0, ∞)` (the paper's own power utility `x ^ γ`, `0 < γ < 1`, is not
differentiable at `0`). Continuity at `0` is implied by the paper's "twice differentiable" for
every utility it differentiates at `0`, and is satisfied by `x ^ γ`. -/
def IsCustomerUtility (u : ℝ → ℝ) : Prop :=
  StrictMonoOn u (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) u ∧ ContinuousOn u (Set.Ici 0) ∧
    (∀ x : ℝ, 0 < x → DifferentiableAt ℝ u x ∧ DifferentiableAt ℝ (deriv u) x) ∧ u 0 = 0

/-- The buy rule of §2.1, p. 1120: facing prices `p₁` (period 1) and `p₂` (period 2) and
anticipated fill rate `q`, a customer with valuation `v` buys in period 1 if and only if
`u (v - p₁) ≥ q * u (v - p₂)` and `v - p₁ ≥ 0`. -/
def buysEarly (u : ℝ → ℝ) (p₁ p₂ q v : ℝ) : Prop :=
  p₁ ≤ v ∧ q * u (v - p₂) ≤ u (v - p₁)

/-- The threshold valuation `v(q)` of §2.1 (Proposition 1, Eq. (2)): the infimum of the
valuations that buy in period 1. Proposition 1 shows that for `q ∈ [0, 1)` the set is nonempty
and bounded below by `p₁`, so this infimum is the paper's cutoff. -/
noncomputable def cutoff (u : ℝ → ℝ) (p₁ p₂ q : ℝ) : ℝ :=
  sInf {v : ℝ | buysEarly u p₁ p₂ q v}

end LiuVanRyzin
