import Mathlib

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), §9.2, p. 202: `u` is the distribution `u_y = P(Y = y)` of a random variable `Y`
taking values in `{1, 2, 3, …}`. It is encoded as a function on `ℕ` with total mass one and no mass
at `0`. -/
def IsDistOnPos (u : ℕ → ℝ≥0∞) : Prop :=
  ∑' y : ℕ, u y = 1 ∧ u 0 = 0

/-- Sennott (1999), §9.2, p. 202: the complement of the cumulative distribution,
`F*(y) = P(Y > y) = ∑_{w > y} u_w`, for `y ≥ 0` (so `F*(0) = 1` when `u` lives on `{1, 2, …}`). -/
noncomputable def tail (u : ℕ → ℝ≥0∞) (y : ℕ) : ℝ≥0∞ :=
  ∑' w : ℕ, if y < w then u w else 0

/-- The `k`-th moment `E[Y^k] = ∑_y y^k u_y ∈ [0, ∞]` of a distribution `u` on `ℕ`
(possibly `+∞`). -/
noncomputable def moment (u : ℕ → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∑' y : ℕ, (y : ℝ≥0∞) ^ k * u y

/-- Sennott (1999), (9.7), p. 203: the distribution of the residual life `Y_s` after `s` completed
slots, `P(Y_s = y) = P(Y = s + y | Y > s) = u_{s+y} / F*(s)` for `y ≥ 1`, and `0` at `y = 0`.
It is meaningful when `F*(s) > 0`; every statement below only uses it under that condition. -/
noncomputable def residualDist (u : ℕ → ℝ≥0∞) (s : ℕ) (y : ℕ) : ℝ≥0∞ :=
  if 1 ≤ y then u (s + y) / tail u s else 0

/-- The `k`-th moment `E[Y_s^k]` of the residual life `Y_s` (in `[0, ∞]`); `k = 1` gives the mean
residual lifetime `E[Y_s]`. -/
noncomputable def residualMoment (u : ℕ → ℝ≥0∞) (s k : ℕ) : ℝ≥0∞ :=
  moment (residualDist u s) k

/-- Sennott (1999), Definition 9.2.4, p. 204: the distribution `u` has bounded mean residual
lifetimes with bound `U` (BMRL-`U`): `E[Y_s] ≤ U` for every `s ≥ 0` at which the residual life is
defined, i.e. `F*(s) = P(Y > s) > 0`. -/
def IsBMRL (u : ℕ → ℝ≥0∞) (U : ℝ≥0) : Prop :=
  ∀ s : ℕ, 0 < tail u s → residualMoment u s 1 ≤ (U : ℝ≥0∞)

/-- Sennott (1999), Definition 9.2.4, p. 204: the distribution `u` is BMRL, i.e. BMRL-`U` for some
finite constant `U`. -/
def IsBMRLDist (u : ℕ → ℝ≥0∞) : Prop :=
  ∃ U : ℝ≥0, IsBMRL u U

end SennottDP.ResidualLife
