import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_LBoundJE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundJE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundIJE

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The inequality system (11.43) with its bounds read in `EReal`, so that the book's `-∞` and
`+∞` cases stay infinite instead of collapsing to `0`. -/
def EquilibriumPricePolyhedronE {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) : Set (K → ℝ) :=
  {p | (∀ j : K, max 0 (LBoundJE U C x y j) ≤ ((p j : ℝ) : EReal) ∧
        ((p j : ℝ) : EReal) ≤ UBoundJE U C x y j) ∧
    ∀ i j : K, i ≠ j → ((p j - p i : ℝ) : EReal) ≤ UBoundIJE U C x y i j}

end DiscreteConvex.EconomicEquilibriumB
