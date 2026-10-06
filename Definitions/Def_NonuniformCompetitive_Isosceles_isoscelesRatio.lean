import Mathlib

namespace NonuniformCompetitive.Isosceles

/-- The number `e_{2d-1} = (1 + 1/(2d-1))^(2d-1) = (2d/(2d-1))^(2d-1)` of Karlin, Manasse,
McGeoch and Owicki (Algorithmica 11 (1994), p. 551 defines `e_p = (1 + 1/p)^p`; p. 566 writes
`e_{2d-1}` out as `(2d/(2d-1))^(2d-1)`). The exponent `2 * d - 1` is a natural number; the
definition is only used for `1 ≤ d`, where it is the paper's exponent (at `d = 0` it is the junk
value `1`). -/
noncomputable def eTwoDSubOne (d : ℕ) : ℝ :=
  ((2 * d : ℝ) / (2 * d - 1)) ^ (2 * d - 1)

/-- The optimal randomized competitive ratio of Theorem 12 (p. 564) for the two-server problem
on the isosceles triangle with edge lengths `1, d, d`:
`(e_{2d-1} + 1/(4d)) / ((e_{2d-1} - 1) + 1/(2d))`.
Only meaningful for `1 ≤ d` (at `d = 0` Lean's division by zero gives the junk value `0`). -/
noncomputable def isoscelesRatio (d : ℕ) : ℝ :=
  (eTwoDSubOne d + 1 / (4 * d)) / ((eTwoDSubOne d - 1) + 1 / (2 * d))

end NonuniformCompetitive.Isosceles
