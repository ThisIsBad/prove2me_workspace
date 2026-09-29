import Mathlib
import Definitions.Def_PLCMarkets_Rationality_RationalityLP

namespace PLCMarkets.Rationality

/-- **§4, second paragraph** (Vazirani–Yannakakis 2011, p. 10:8): any optimal solution of the LP
constructed from the equilibrium prices `p'` gives equilibrium prices. The prices `p'` are
positive and sum to the total money (the standing assumptions of Section 3 under which the LP's
data are defined); the optimal solution's prices are
assumed positive, which the page leaves implicit. -/
theorem isEquilibrium_of_lpOptimal {n g : ℕ} (M : FisherMarket n g) (p' : Fin g → ℝ)
    (hp' : M.IsEquilibrium p')
    (hpos : ∀ j, 0 < p' j)
    (hsum : ∑ j, p' j = ∑ i, (M.budget i : ℝ))
    (z : FisherMarket.LPPoint n g) (hz : M.IsLPOptimal p' z)
    (hzpos : ∀ j, 0 < z.p j) :
    M.IsEquilibrium z.p := by sorry

end PLCMarkets.Rationality
