import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model

namespace CongestionPoA.Mixed

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 6, Theorem 14: the mixed price of anarchy of linear congestion games for the average social
cost is at most `(3 + √5)/2 ≈ 2.618`. For every congestion game with linear latencies, every mixed
Nash equilibrium `σ` and every pure strategy profile `P`,
`Σᵢ E[cᵢ] ≤ ((3 + √5)/2)·SUM(P)`.

**Formalization Note.** "Linear" is the paper's `f_e(k) = a_e·k + b_e` with `a_e, b_e ≥ 0` (Sect. 2).
The social cost of the mixed equilibrium is the first option of Sect. 5, the sum of the players'
expected costs (`mixedSumCost`); the optimum is `opt = min_{P∈Σ} SUM(P)` over pure profiles (Sect. 2).
Bounding by `SUM(P)` for every feasible pure `P` is equivalent to `PA ≤ (3+√5)/2`, since there are
finitely many pure profiles; no ratio is formed, so `opt = 0` needs no special case. Mixed equilibria
are independent randomizations (`AGT.IsMixedNash` with payoff `−cost`); a correlated distribution on
profiles is not covered. -/
theorem mixed_poa_sum_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hlin : CongestionPoA.AsymSum.IsLinear G)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    mixedSumCost G σ ≤ (3 + Real.sqrt 5) / 2 * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.Mixed

