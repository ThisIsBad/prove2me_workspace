import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325, Eq. (11.8) (the notation `U[−p]` used
throughout section 11.3, e.g. p.330): the price-shifted utility, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The price-shifted utility `U[−p](x) = U(x) − ⟨p,x⟩` for a utility-type function
`U : Zᴷ → R ∪ {−∞}` and a price vector `p ∈ Rᴷ`. -/
def PriceShift {K : Type*} [Fintype K] (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x : K → ℤ) :
    WithBot ℝ :=
  U x + ((-(∑ k, p k * (x k : ℝ)) : ℝ) : WithBot ℝ)

end DiscreteConvex.EconomicEquilibrium
