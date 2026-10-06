import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model

open MeasureTheory Set

namespace ServiceParts.BaseStock

/-- The quantity minimised in the recursion of p. 18 when the continuation value is `V`:
`c·u + L(y) + α ∫₀^∞ V(y + u − x) g(x) dx`, for inventory position `y` and order `u`. -/
noncomputable def Model.stageCost (M : Model) (V : ℝ → ℝ) (y u : ℝ) : ℝ :=
  M.c * u + M.L y + M.α * ∫ x in Ioi (0 : ℝ), V (y + u - x) * M.g x

/-- The n-period value functions `f n` = the book's `fₙ` (p. 18 and p. 21), lead time τ = 1:
`f₁(y) = L(y)` and `fₙ(y) = min_{u ≥ 0} {c·u + L(y) + α ∫₀^∞ fₙ₋₁(y + u − x) g(x) dx}` for
`n ≥ 2`, the minimum written as the infimum over `u ≥ 0`. The value at index `0` is the
constant `0`; it is not used by any statement of the mission. -/
noncomputable def Model.f (M : Model) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => M.L
  | n + 2 => fun y => sInf (M.stageCost (M.f (n + 1)) y '' Ici 0)

/-- The objective of the `n`-period problem at inventory position `y` and order quantity `u`
(meaningful for `n ≥ 2`): `c·u + L(y) + α ∫₀^∞ fₙ₋₁(y + u − x) g(x) dx`. -/
noncomputable def Model.orderCost (M : Model) (n : ℕ) (y u : ℝ) : ℝ :=
  M.stageCost (M.f (n - 1)) y u

/-- `u` is an optimal order in the `n`-period problem at inventory position `y`: `u ≥ 0` and
it minimises the objective over **all** order quantities `u' ≥ 0`. -/
def Model.IsOptimalOrder (M : Model) (n : ℕ) (y u : ℝ) : Prop :=
  0 ≤ u ∧ ∀ u' : ℝ, 0 ≤ u' → M.orderCost n y u ≤ M.orderCost n y u'

/-- The order-up-to rule with level `s`, `u(y) = max{0, s − y}` (eq. (2.5)), is optimal in the
`n`-period problem at every inventory position `y`. -/
def Model.IsOrderUpToOptimal (M : Model) (n : ℕ) (s : ℝ) : Prop :=
  ∀ y : ℝ, M.IsOptimalOrder n y (max 0 (s - y))

/-- The function `Fₙ(w) = c + α ∫₀^∞ f′ₙ(w − x) g(x) dx` of eq. (2.8), p. 19. -/
noncomputable def Model.F (M : Model) (n : ℕ) (w : ℝ) : ℝ :=
  M.c + M.α * ∫ x in Ioi (0 : ℝ), deriv (M.f n) (w - x) * M.g x

end ServiceParts.BaseStock
