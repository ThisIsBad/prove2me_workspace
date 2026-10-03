import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_LBCirc
import Definitions.Def_DiscreteConvex_AlgorithmsB_UBCirc

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `B° = {y∈B | ℓ°_B ≤ y ≤ u°_B}`, the central part of `B`. -/
def BCirc (B : Set (V → ℤ)) : Set (V → ℤ) :=
  {y ∈ B | ∀ v, LBCirc B v ≤ (y v : ℚ) ∧ (y v : ℚ) ≤ UBCirc B v}

end DiscreteConvex.AlgorithmsB
