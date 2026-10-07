import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle

namespace ShapleyScarf.TopTrading

/-- §6, p. 114: every nonempty set of traders `R` has at least one top trading cycle. -/
theorem exists_topTradingCycle {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ)
    (R : Finset N) (hR : R.Nonempty) :
    ∃ (S : Finset N) (next : N → N), IsTopTradingCycle A R S next := by sorry

end ShapleyScarf.TopTrading

