import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_Nondecreasing
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_BoundedSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsEquilibrium

namespace DiscreteConvex.EconomicEquilibrium

/-- Theorem 11.13 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.337), the goal theorem of this
mission: existence of equilibrium in an exchange economy. Consider an exchange economy (no
producers, `L = PEmpty`) with agents indexed by `H`, and suppose that `Uh` (`h ∈ H`) are
nondecreasing M♮-concave functions with `dom Uh` bounded. Then there exists an equilibrium
`((xh | h ∈ H), p)` for every total initial endowment `x° ∈ ⋂_{h ∈ H} dom Uh`. -/
theorem exchange_economy_equilibrium_exists {H K : Type*} [Fintype H] [Fintype K] [DecidableEq K]
    (U : H → (K → ℤ) → WithBot ℝ) (hU : ∀ h, MNaturalConcave (U h))
    (hUnd : ∀ h, Nondecreasing (U h)) (hUb : ∀ h, BoundedSet (UDom (U h)))
    (x0 : K → ℤ) (hx0 : ∀ h, x0 ∈ UDom (U h)) :
    ∃ (x : H → (K → ℤ)) (p : K → ℝ),
      IsEquilibrium U (fun l : PEmpty => l.elim) x0 x (fun l : PEmpty => l.elim) p := by sorry

end DiscreteConvex.EconomicEquilibrium
