import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325, Eq. (11.8) (the demand set `Dh(p) = arg
max_x (Uh(x) − ⟨p,x⟩)`): the maximizer set of a `WithBot ℝ`-valued function, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The maximizer set `arg max g = {x ∈ Zᴷ : g(x) ≥ g(y) ∀y ∈ Zᴷ}` of `g : Zᴷ → R ∪ {−∞}`. -/
def ArgMaxBot {K : Type*} (g : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) :=
  {x | ∀ y, g y ≤ g x}

end DiscreteConvex.EconomicEquilibrium
