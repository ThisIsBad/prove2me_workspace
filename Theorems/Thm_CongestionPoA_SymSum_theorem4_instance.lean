import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 4, Theorem 4: there are instances of symmetric linear congestion games for which the price of
anarchy of the average social cost is `(5N − 2)/(2N + 1)`. Stated as: for every number of players
`N ≥ 1` there is a symmetric linear congestion game with players `Fin N` and finitely many
facilities, a pure Nash equilibrium `A` and a pure strategy profile `P` with `SUM(P) > 0` and
`SUM(A) = ((5N − 2)/(2N + 1))·SUM(P)`.

**Formalization Note.** Together with Theorem 3 the equality gives `PA = (5N − 2)/(2N + 1)` for this
game (`P` then attains `opt`). The condition `SUM(P) > 0` excludes the trivial witness with zero
latencies (or empty strategies), where `0 = c · 0` for every `c`. Linear latencies are
`f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0`. The paper's construction (facilities partitioned into
`P₁, …, P_N`, each with `Nα₁ + C(N,2)α₂` facilities, `α₁ = N + 2`, `α₂ = 2`, common strategy set
`{P₁, …, P_N, A₁, …, A_N}`, identity latencies) is one witness; the statement does not fix it. -/
theorem theorem4_instance (N : ℕ) (hN : 1 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      CongestionPoA.AsymSum.IsLinear G ∧ IsSymmetric G ∧ CongestionPoA.AsymSum.IsPureNash G A ∧ CongestionPoA.AsymSum.IsProfile G P ∧ 0 < CongestionPoA.AsymSum.sumCost G P ∧
        CongestionPoA.AsymSum.sumCost G A = (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.SymSum

