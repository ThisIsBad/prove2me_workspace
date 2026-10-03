import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325 (general notation `dom U`, e.g. used in
Theorem 11.4, p.330): the effective domain of a utility-type function `U : ZK → R ∪ {−∞}`, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The effective domain `dom U = {x ∈ Zᴷ : U(x) ≠ −∞}` of a utility-type function
`U : Zᴷ → R ∪ {−∞}`. The `WithBot ℝ`-valued counterpart of `DiscreteConvex.MConvexFunctions.DomZ`
(which is stated for `WithTop ℝ`-valued cost-type functions). -/
def UDom {K : Type*} (U : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) :=
  {x | U x ≠ ⊥}

end DiscreteConvex.EconomicEquilibrium
