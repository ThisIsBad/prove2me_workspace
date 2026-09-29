import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- LEMMA B (Luby 1986, §3.4, p. 1042). For Algorithm B and every vertex `i` with `d(i) ≥ 1`,
`Pr[i ∈ N(I′)] ≥ ¼ · min {sum(i)/2, 1}`. -/
theorem lemmaB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) (hi : 1 ≤ H.degree i) :
    probB H (fun c => i ∈ nbhd H (selectB H c)) ≥ 1 / 4 * min (sumInv H i / 2) 1 := by sorry

end LubyMIS.MonteCarlo

