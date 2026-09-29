import Mathlib
import Definitions.Def_PLCMarkets_Rationality_RationalityLP

namespace PLCMarkets.Rationality

/-- **Proof of THEOREM 4.1, first sentence** (Vazirani–Yannakakis 2011, §4, p. 10:9): the
starting equilibrium prices `p'`, together with a flow, form an optimal solution of value `M`
(the total money of the buyers) of the LP constructed from `p'`. The prices `p'` are positive and sum
to the total money (the standing assumptions of Section 3 under which the LP's data are
defined). -/
theorem lp_optimal_value_eq_total_money {n g : ℕ} (M : FisherMarket n g) (p' : Fin g → ℝ)
    (hp' : M.IsEquilibrium p')
    (hpos : ∀ j, 0 < p' j)
    (hsum : ∑ j, p' j = ∑ i, (M.budget i : ℝ)) :
    ∃ z : FisherMarket.LPPoint n g, z.p = p' ∧ M.IsLPOptimal p' z ∧
      M.lpObjective p' z = ∑ i, (M.budget i : ℝ) := by sorry

end PLCMarkets.Rationality
