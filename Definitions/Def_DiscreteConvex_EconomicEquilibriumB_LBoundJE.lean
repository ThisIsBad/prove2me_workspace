import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToEReal
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- `ℓ(j)`, Eq. (11.40), computed in `EReal`. `LBoundJ` reads the book's `-∞` and `+∞` cases as
`0` through `unbotD 0`/`untopD 0`, which turns an unattainable bundle into a finite bound and
refutes Theorems 11.21 and 11.22 (one good, one consumer with `U(0) = U(1) = 0`, `U(2) = 5` and
`-∞` elsewhere, one producer with `C` the indicator of `0`: the equilibrium price set is
`{p ≥ 5/2}` while the real-valued system gives `{0}`). -/
noncomputable def LBoundJE {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) (j : K) : EReal :=
  max
    ((Finset.univ : Finset H).sup' Finset.univ_nonempty
      (fun h => ToERealOfBot (U h (fun k => x h k + (if k = j then (1:ℤ) else 0))) -
        ToERealOfBot (U h (x h))))
    ((Finset.univ : Finset L).sup' Finset.univ_nonempty
      (fun l => ToEReal (C l (y l)) -
        ToEReal (C l (fun k => y l k - (if k = j then (1:ℤ) else 0)))))

end DiscreteConvex.EconomicEquilibriumB
