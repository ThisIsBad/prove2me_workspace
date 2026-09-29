import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- Closing chain of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), with the common factor `⅛`
divided out: `½ ∑_{sum(i) ≤ 2} d(i) sum(i) + ∑_{sum(i) > 2} d(i) ≥ |E′|`. -/
theorem degree_sum_ge_edges {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2), (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) ≥
      (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.MonteCarlo
