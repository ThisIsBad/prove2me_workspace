import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShiftConvex
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ArgMinTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.324, Eq. (11.1): the supply set of a producer, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The supply set `Sl(p) = arg max_{y ∈ Zᴷ} (⟨p,y⟩ − Cl(y))` (Eq. (11.1)) of a producer with cost
function `Cl` at price `p`, restated equivalently as `arg min Cl[−p]` (the book's own notation
from p.336 on: `yl ∈ arg min Cl[−p]`). -/
def SupplySet {K : Type*} [Fintype K] (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℤ) :=
  ArgMinTop (PriceShiftConvex C p)

end DiscreteConvex.EconomicEquilibrium
