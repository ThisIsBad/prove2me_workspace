import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace OnlinePrimalDual.GeneralPacking

/-- `aᵢ(max) = maxₖ{a(i,k)}` (Buchbinder & Naor, FnT TCS 2009, Theorem 14.1, p. 249): the largest
coefficient of primal variable `i` across every constraint. -/
noncomputable def aMax {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (inst : GeneralInstance I J) (i : I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (inst.a i)

end OnlinePrimalDual.GeneralPacking
