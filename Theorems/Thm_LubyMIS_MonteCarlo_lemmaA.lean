import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- LEMMA A (Beame) (Luby 1986, §3.4, p. 1041). For Algorithm A and every vertex `i` with
`d(i) ≥ 1`, `Pr[i ∈ N(I′)] ≥ [¼ · min {sum(i), 1}] · (1 − 1/(2n²))`. -/
theorem lemmaA {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] (i : V)
    (hi : 1 ≤ H.degree i) :
    probA n (fun π => i ∈ nbhd H (selectA H π)) ≥
      (1 / 4 * min (sumInv H i) 1) * (1 - 1 / (2 * (n : ℝ) ^ 2)) := by sorry

end LubyMIS.MonteCarlo
