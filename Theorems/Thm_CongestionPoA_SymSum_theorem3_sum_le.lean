import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Theorem 3: for linear symmetric congestion games, the pure price of anarchy of the average
social cost is at most `(5N − 2)/(2N + 1)`, `N` the number of players. Stated as: for every pure
Nash equilibrium `A` and every pure strategy profile `P`, `SUM(A) ≤ ((5N − 2)/(2N + 1))·SUM(P)`.

**Formalization Note.** Since `opt = min_P SUM(P)` is attained (finitely many profiles), the bound for
every profile `P` is equivalent to `PA ≤ (5N − 2)/(2N + 1)`, without dividing by `opt`. Linear means
`f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0` (`IsLinear`); symmetric means all players share one
strategy set (`IsSymmetric`). Players are `Fin N` with `1 ≤ N`; the constant is computed in `ℝ`. -/
theorem theorem3_sum_le {N : ℕ} (hN : 1 ≤ N) {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (hlin : CongestionPoA.AsymSum.IsLinear G) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    CongestionPoA.AsymSum.sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.SymSum

