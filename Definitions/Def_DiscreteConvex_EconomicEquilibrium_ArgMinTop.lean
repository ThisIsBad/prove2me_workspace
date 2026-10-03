import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.324, Eq. (11.1), restated via the `Cl[−p]`
notation used from p.336 on (`yl ∈ arg min Cl[−p]`): the minimizer set of a `WithTop ℝ`-valued
function, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The minimizer set `arg min f = {x ∈ Zᴷ : f(x) ≤ f(y) ∀y ∈ Zᴷ}` of `f : Zᴷ → R ∪ {+∞}`. -/
def ArgMinTop {K : Type*} (f : (K → ℤ) → WithTop ℝ) : Set (K → ℤ) :=
  {x | ∀ y, f x ≤ f y}

end DiscreteConvex.EconomicEquilibrium
