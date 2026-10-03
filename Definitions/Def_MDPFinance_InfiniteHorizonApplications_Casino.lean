import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- The red-and-black gambling model (Bäuerle–Rieder, §7.6.3, p. 226-227, PDF 237-238): state
space `E := \{0,\dots,B\}` (current fortune, rendered as `Fin (B+1)`), win probability `p \in
(0,1)`, feasible bets `D(x) := \{0,\dots,\min(x,B-x)\}`; win moves `x \mapsto x+a`, lose moves
`x \mapsto x-a` (each with the obvious probability), absorbing at `0` and `B`; reward `1` only
upon reaching `B`, `\beta := 1`. Bespoke real-valued/probabilistic operators (not the generic
`Kernel`-based model) since the transition is an elementary two-point distribution. -/
structure CasinoMarket where
  B : ℕ
  p : ℝ
  hp0 : 0 < p
  hp1 : p < 1

/-- `D(x) := \{0,\dots,\min(x,B-x)\}`, the feasible bets at fortune `x`. -/
def CasinoMarket.D (Mk : CasinoMarket) (x : Fin (Mk.B + 1)) : Finset ℕ :=
  Finset.range (min x.1 (Mk.B - x.1) + 1)

/-- The value-to-go `V_n^π(x)` of a (possibly nonstationary) Markov policy `π = (f_0,f_1,…)` after
`n` further games (peeling `f_0` off),
truncating a bet at `\min(f(x),\min(x,B-x))` to stay feasible regardless of `f`'s own values off
`D(x)` (Bäuerle–Rieder, p. 227, PDF 238, the reward-iteration recursion `T_fV_{n-1}`; base case
`1` at `x=B`, `0` at `x=0` or `n=0` with `0<x<B`). -/
noncomputable def CasinoMarket.VpiSeq (Mk : CasinoMarket) (π : ℕ → Fin (Mk.B + 1) → ℕ) :
    ℕ → Fin (Mk.B + 1) → ℝ
  | 0, x => if x.1 = Mk.B then 1 else 0
  | (n + 1), x =>
      if x.1 = 0 ∨ x.1 = Mk.B then (if x.1 = Mk.B then (1 : ℝ) else 0)
      else
        let a := min (π 0 x) (min x.1 (Mk.B - x.1))
        Mk.p * VpiSeq Mk (fun k => π (k + 1)) n ⟨x.1 + a, by omega⟩ +
          (1 - Mk.p) * VpiSeq Mk (fun k => π (k + 1)) n ⟨x.1 - a, by omega⟩

/-- `V_n^f`, the value-to-go of the stationary rule `f`. -/
noncomputable def CasinoMarket.Vpi (Mk : CasinoMarket) (f : Fin (Mk.B + 1) → ℕ) :
    ℕ → Fin (Mk.B + 1) → ℝ :=
  Mk.VpiSeq (fun _ => f)

/-- The **timid strategy** `f_*(x) := 1` for `x > 0`, `f_*(0) := 0` (Bäuerle–Rieder, p. 227, PDF
238). -/
def CasinoMarket.timid (Mk : CasinoMarket) (x : Fin (Mk.B + 1)) : ℕ :=
  if x.1 = 0 then 0 else 1

/-- The **bold strategy** `f_{**}(x) := \min\{x,B-x\}` (Bäuerle–Rieder, p. 228, PDF 239). -/
def CasinoMarket.bold (Mk : CasinoMarket) (x : Fin (Mk.B + 1)) : ℕ :=
  min x.1 (Mk.B - x.1)

/-- `J_\infty^f(x) := \sup_n V_n^f(x)`, the value of a stationary betting rule `f` over infinitely
many games (the win probability under `f^\infty`; equals `\lim_n V_n^f(x)` since `(V_n^f)` is
increasing in `n`, matching the positive-model convention of chunk `07b`). -/
noncomputable def CasinoMarket.Jinfpi (Mk : CasinoMarket) (f : Fin (Mk.B + 1) → ℕ)
    (x : Fin (Mk.B + 1)) : ℝ :=
  ⨆ n, Mk.Vpi f n x

/-- `J_\infty(x) := \sup_{π ∈ F^∞} J_\infty^π(x)`, the maximal probability of reaching `B` before
`0`, over all Markov policies `π = (f_0,f_1,…)` (not only stationary ones). -/
noncomputable def CasinoMarket.Jinf (Mk : CasinoMarket) (x : Fin (Mk.B + 1)) : ℝ :=
  ⨆ π : ℕ → Fin (Mk.B + 1) → ℕ, ⨆ n, Mk.VpiSeq π n x

end MDPFinance.InfiniteHorizonApplications
