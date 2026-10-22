import Definitions.Def_CarryRNG_AWC_Lags

namespace CarryRNG.AWC

/-- A state (seed vector) `(x_1, …, x_r, c)`: `r` base-`b` digits and a carry bit.
Lean index `i : Fin r` is the paper's `x_{i+1}`, so `x 0` is `x_1`, the oldest digit. -/
structure State (b r : ℕ) where
  x : Fin r → Fin b
  c : Fin 2
  deriving DecidableEq, Fintype

end CarryRNG.AWC
