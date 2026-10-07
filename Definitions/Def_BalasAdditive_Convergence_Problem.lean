import Mathlib
import Definitions.Def_BalasAdditive_Convergence_BinaryLP

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Balas's problem P: a zero-one program with nonnegative objective coefficients. -/
structure Problem (n m : ℕ) where
  lp : BinaryLP n m
  hc : ∀ j, 0 ≤ lp.c j

end BalasAdditive.Convergence
