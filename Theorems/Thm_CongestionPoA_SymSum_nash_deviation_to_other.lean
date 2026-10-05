import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, unnumbered step of the proof of Theorem 3: in a symmetric game every strategy is
available to every player, so at a pure Nash equilibrium `A` the cost of player `i` is at most the
cost of deviating to the strategy `Pⱼ` of any player `j` in any pure strategy profile `P`:
`cᵢ(A) ≤ Σ_{e∈Pⱼ} n_e(A) + |Pⱼ − Aᵢ|`.

**Formalization Note.** The paper displays the identity latencies `f_e(k) = k`; for the linear
latencies `f_e(k) = a_e k + b_e` (`a_e, b_e ≥ 0`) of Sect. 2 the right-hand side is
`Σ_{e∈Pⱼ} (a_e n_e(A) + b_e) + Σ_{e∈Pⱼ∖Aᵢ} a_e`, which is the printed one when `a_e = 1`,
`b_e = 0`. The coefficients are explicit binders. Players are `Fin N`; `Pⱼ ∈ Σᵢ` follows from
`P` being a profile and the game being symmetric. -/
theorem nash_deviation_to_other {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlin : ∀ e k, G.latency e k = a e * k + b e) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) (i j : Fin N) :
    CongestionPoA.AsymSum.cost G A i ≤ ∑ e ∈ P j, (a e * (CongestionPoA.AsymSum.load A e : ℝ) + b e) + ∑ e ∈ P j \ A i, a e := by sorry

end CongestionPoA.SymSum

