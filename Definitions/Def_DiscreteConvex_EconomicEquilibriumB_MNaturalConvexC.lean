import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppPos
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppNeg

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- M♮-convexity of a cost function `C : Zᴷ → R ∪ {+∞}`, the mirror of `MNaturalConcave`.
Murota, *Discrete Convex Analysis*, SIAM 2003, §11.5 assumes it of every producer's cost. -/
def MNaturalConvexC (C : (K → ℤ) → WithTop ℝ) : Prop :=
  {z | C z ≠ ⊤}.Nonempty ∧
  ∀ x, C x ≠ ⊤ → ∀ y, C y ≠ ⊤ → ∀ i ∈ SuppPos x y,
    C x + C y ≥ min
      (C (fun w => x w - (if w = i then (1:ℤ) else 0)) +
        C (fun w => y w + (if w = i then (1:ℤ) else 0)))
      ((SuppNeg x y).inf (fun j =>
        C (fun w => x w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) +
          C (fun w => y w + (if w = i then (1:ℤ) else 0) - (if w = j then (1:ℤ) else 0))))

end DiscreteConvex.EconomicEquilibriumB
