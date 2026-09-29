import Mathlib

namespace MakeToStockRM.ExpDensity

/-- The region `Ω = {(x, y) : y_min < y < y_max, η(y) < x < ξ(y)}` of (34)
(Caldentey–Wein 2006, p. 866): points are `(x, y)` with `x` the inventory and `y` the log-price;
`η` is the rejection (lower) boundary and `ξ` the idleness (upper) boundary. -/
def region (η ξ : ℝ → ℝ) (ymin ymax : ℝ) : Set (ℝ × ℝ) :=
  {z | ymin < z.2 ∧ z.2 < ymax ∧ η z.2 < z.1 ∧ z.1 < ξ z.2}

end MakeToStockRM.ExpDensity
