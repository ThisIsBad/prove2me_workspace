import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_LBCirc
import Definitions.Def_DiscreteConvex_AlgorithmsB_UBCirc
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `V°(x) = {v∈V | ℓ°_B(v) ≤ x(v) ≤ u°_B(v)}`. -/
noncomputable def VCirc (B : Set (V → ℤ)) (x : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => LBCirc B v ≤ (x v : ℚ) ∧ (x v : ℚ) ≤ UBCirc B v)

-- ===== Submodular set functions and base polyhedra (§10.2.1) =====

end DiscreteConvex.AlgorithmsB
