import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.324, Eq. (11.1), and the notation `Cl[−p]` used
from p.336 on: the price-shifted cost, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The price-shifted cost `C[−p](y) = C(y) − ⟨p,y⟩` for a cost-type function
`C : Zᴷ → R ∪ {+∞}` and a price vector `p ∈ Rᴷ`. -/
def PriceShiftConvex {K : Type*} [Fintype K] (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) (y : K → ℤ) :
    WithTop ℝ :=
  C y + ((-(∑ k, p k * (y k : ℝ)) : ℝ) : WithTop ℝ)

end DiscreteConvex.EconomicEquilibrium
