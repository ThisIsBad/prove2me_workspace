import Mathlib

namespace RevShareCoord.Single

/-- Realized retailer profit in the fixed-price newsvendor of Sec. 2.3 (p. 8–9) under the
buy-back contract `{b, w_b}`: retail price `p`, order `q`, realized demand `D`; the retailer
sells `min(q, D)` units at `p`, returns the `(q − D)⁺` leftover units for `b` each (salvage value
normalized to zero, Sec. 1), and pays `w_b` per unit ordered. -/
def bbRetailerRealized (p b wb q D : ℝ) : ℝ :=
  p * min q D + b * max (q - D) 0 - wb * q

/-- Realized supplier profit under the buy-back contract `{b, w_b}` with unit production cost
`c`: she receives `w_b q`, pays `b` for each of the `(q − D)⁺` returned units, and produces `q`
units at cost `c`. -/
def bbSupplierRealized (b wb c q D : ℝ) : ℝ :=
  wb * q - b * max (q - D) 0 - c * q

/-- Realized retailer profit under the revenue-sharing contract `{φ, w}`: he keeps the share
`φ` of the realized revenue `p · min(q, D)` and pays `w` per unit ordered. -/
def rsRetailerRealized (p φ w q D : ℝ) : ℝ :=
  φ * (p * min q D) - w * q

/-- Realized supplier profit under the revenue-sharing contract `{φ, w}` with unit production
cost `c`: she receives `(1 − φ) p · min(q, D)` and `wq`, and produces `q` units at cost `c`. -/
def rsSupplierRealized (p φ w c q D : ℝ) : ℝ :=
  (1 - φ) * (p * min q D) + w * q - c * q

end RevShareCoord.Single
