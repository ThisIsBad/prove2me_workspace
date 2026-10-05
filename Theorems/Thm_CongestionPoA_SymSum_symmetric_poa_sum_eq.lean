import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF pp. 3–4, Theorems 3 and 4: for symmetric linear congestion games with `N` players the pure price
of anarchy of the average social cost is exactly `(5N − 2)/(2N + 1)`. For every `N ≥ 1`:
(Theorem 3) every pure Nash equilibrium `A` of every symmetric linear congestion game with players
`Fin N` satisfies `SUM(A) ≤ ((5N − 2)/(2N + 1))·SUM(P)` for every pure strategy profile `P`; and
(Theorem 4) some symmetric linear game with players `Fin N` has a pure Nash equilibrium `A` and a
profile `P` with `SUM(P) > 0` and `SUM(A) = ((5N − 2)/(2N + 1))·SUM(P)`.

**Formalization Note.** The bound for every profile `P` is equivalent to `PA ≤ (5N − 2)/(2N + 1)`
(the optimum is attained); with the second part it gives `PA = (5N − 2)/(2N + 1)` as a worst case over
the class. `SUM(P) > 0` excludes the trivial all-zero witness. Linear latencies are
`f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0`; the paper's proofs display `f_e(k) = k`. Facility types
range over `Type` with `Fintype` and `DecidableEq`. -/
theorem symmetric_poa_sum_eq (N : ℕ) (hN : 1 ≤ N) :
    (∀ (E : Type) [Fintype E] [DecidableEq E] (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        CongestionPoA.AsymSum.IsLinear G → IsSymmetric G → CongestionPoA.AsymSum.IsPureNash G A → CongestionPoA.AsymSum.IsProfile G P →
          CongestionPoA.AsymSum.sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P) ∧
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      CongestionPoA.AsymSum.IsLinear G ∧ IsSymmetric G ∧ CongestionPoA.AsymSum.IsPureNash G A ∧ CongestionPoA.AsymSum.IsProfile G P ∧ 0 < CongestionPoA.AsymSum.sumCost G P ∧
        CongestionPoA.AsymSum.sumCost G A = (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.SymSum

