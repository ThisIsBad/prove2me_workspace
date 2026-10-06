import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppPos
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppNeg

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `U : Zᴷ → R∪{−∞}` is M♮-concave (axiom (−M♮-EXC[Z]), Eq. (11.17)). -/
def MNaturalConcave (U : (K → ℤ) → WithBot ℝ) : Prop :=
  (UDom U).Nonempty ∧
  ∀ x ∈ UDom U, ∀ y ∈ UDom U, ∀ i ∈ SuppPos x y,
    U x + U y ≤ max
      (U (fun w => x w - (if w = i then (1:ℤ) else 0)) + U (fun w => y w + (if w = i then (1:ℤ) else 0)))
      ((SuppNeg x y).sup (fun j =>
        U (fun w => x w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) +
          U (fun w => y w + (if w = i then (1:ℤ) else 0) - (if w = j then (1:ℤ) else 0))))

end DiscreteConvex.EconomicEquilibriumB
