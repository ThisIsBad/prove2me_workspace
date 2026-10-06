import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorem 8: there are instances of symmetric congestion games for which the price of anarchy
is `(5N+1)/(2N+2)`, for maximum social cost. Stated as: for every `N ≥ 3` there is a symmetric linear
congestion game with players `Fin N` and finitely many facilities, a pure Nash equilibrium `A` and a
pure profile `P` that minimizes the maximum social cost, with `MAX(P) > 0` and
`MAX(A) = ((5N+1)/(2N+2))·MAX(P)`.

**Formalization Note.** The conclusion gives `PA ≥ (5N+1)/(2N+2)` for the instance (`P` attains the
optimum `min_Q MAX(Q)`, `A` is a Nash equilibrium); this is what the paper's proof establishes — it
does not show that `A` is a worst equilibrium. `MAX(P) > 0` excludes the trivial witness with all
costs `0`. The paper's construction uses identity latencies `f_e(k) = k`, which are linear, so the
word "linear" omitted in the theorem's sentence is harmless (the section is about linear latencies).
`N ≥ 3` is the range of the construction (its equation (2) has the factor `N − 3`, and `α₂ = 0` at
`N = 3`); the paper leaves the range implicit. `[NeZero N]` only supplies the nonempty player set
`MAX` needs and is implied by `3 ≤ N`. The statement does not fix the construction. -/
theorem theorem8_instance (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsSymmetric G ∧ IsPureNash G A ∧ IsProfile G P ∧
      (∀ Q : Fin N → Finset E, IsProfile G Q → maxCost G P ≤ maxCost G Q) ∧
      0 < maxCost G P ∧
      maxCost G A = (5 * N + 1) / (2 * N + 2) * maxCost G P := by sorry

end CongestionPoA.SymMax

