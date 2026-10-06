import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToEReal
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `u(i,j)`, Eq. (11.42), computed in `EReal` so that an unattainable bundle leaves the bound
infinite rather than `0`. -/
noncomputable def UBoundIJE {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (i j : K) : EReal :=
  min
    ((Finset.univ : Finset H).inf' Finset.univ_nonempty
      (fun h => ToERealOfBot (U h (x h)) -
        ToERealOfBot (U h (fun k => x h k + (if k = i then (1:ℤ) else 0) -
          (if k = j then (1:ℤ) else 0)))))
    ((Finset.univ : Finset L).inf' Finset.univ_nonempty
      (fun l => ToEReal (C l (fun k => y l k - (if k = i then (1:ℤ) else 0) +
        (if k = j then (1:ℤ) else 0))) - ToEReal (C l (y l))))

end DiscreteConvex.EconomicEquilibriumB
