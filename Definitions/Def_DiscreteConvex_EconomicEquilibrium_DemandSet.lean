import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShift
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ArgMaxBot

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325, Eq. (11.8): the demand set of a consumer, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The demand set `Dh(p) = arg max_{x ∈ Zᴷ} (Uh(x) − ⟨p,x⟩)` (Eq. (11.8)) of a consumer with
utility function `Uh` at price `p`. -/
def DemandSet {K : Type*} [Fintype K] (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℤ) :=
  ArgMaxBot (PriceShift U p)

end DiscreteConvex.EconomicEquilibrium
