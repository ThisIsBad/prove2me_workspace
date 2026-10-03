import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.5.4 (Bäuerle–Rieder, p. 113, PDF 127). a) `V_n` is concave, increasing and
homogeneous of degree `γ` on `E`, `V_N(x) = U(x_0+x_1)`, `V_n(x) = sup_{0≤a≤x_1+x_0/(1+c)}
𝔼[V_{n+1}(h(x,a)(1+i_{n+1}), a\,\tilde R_{n+1})]`. b) The optimal amount invested in the stock at
time `n` is the three-region rule (4.32) with thresholds `q^±(V_{n+1})` of (4.30)/(4.31). The
thresholds are given through the largest maximizers `a^+_n ∈ [0,1]`, `a^-_n ∈ [0,1/(1+c)]` of the
one-period problems at the states `(0,1)` and `(1,0)` (the book's transformation
`q = a/((1-c)(1-a))`, which also covers `q^+ = ∞`, i.e. `a^+ = 1`): `q^+(V_{n+1}) =
a^+_n/((1-c)(1-a^+_n))` (or `∞`) and `q^-(V_{n+1}) = a^-_n/(1-(1+c)a^-_n)` (or `∞`), and on the
sell region `f_n^*(x) = (x_1 + x_0/(1-c)) a^+_n = (x_0+(1-c)x_1) q^+ / (1+(1-c)q^+)`, on the buy
region `f_n^*(x) = (x_0+(1+c)x_1) a^-_n = (x_0+(1+c)x_1) q^- / (1+(1+c)q^-)`, and `f_n^*(x) = x_1` on
the hold region; the optimal bond holding is `h(x, f_n^*(x))`, and the strategy is optimal. -/
theorem transaction_cost_solution {Ω : Type*} [MeasurableSpace Ω] (M : TransactionCostMarket Ω) :
    (∀ n ≤ M.N, IsInIM M.γ (fun x => M.V n x.1 x.2)) ∧
      (∀ x ∈ Estate, M.V M.N x.1 x.2 = M.U (x.1 + x.2)) ∧
      (∀ n < M.N, ∀ x ∈ Estate,
        M.V n x.1 x.2 = ⨆ a ∈ M.Arange x.1 x.2,
          ∫ ω, M.V (n + 1) (M.h x.1 x.2 a * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
      (∃ ap am : ℕ → ℝ, ∀ n < M.N,
        (ap n ∈ Set.Icc (0 : ℝ) 1 ∧
          (∀ a ∈ Set.Icc (0 : ℝ) 1,
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP ≤
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - ap n) * (1 + M.i (n + 1)))
              (ap n * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) 1,
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP =
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - ap n) * (1 + M.i (n + 1)))
              (ap n * M.Rtilde (n + 1) ω) ∂M.measIP → a ≤ ap n)) ∧
        (am n ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP ≤
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * am n) * (1 + M.i (n + 1)))
              (am n * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP =
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * am n) * (1 + M.i (n + 1)))
              (am n * M.Rtilde (n + 1) ω) ∂M.measIP → a ≤ am n)) ∧
        ∃ fstar : ℕ → ℝ × ℝ → ℝ,
          (∀ n < M.N, ∀ x ∈ Estate,
            let qp : EReal := if ap n < 1 then ((ap n / ((1 - M.c) * (1 - ap n)) : ℝ) : EReal) else ⊤
            let qm : EReal :=
              if am n < 1 / (1 + M.c) then ((am n / (1 - (1 + M.c) * am n) : ℝ) : EReal) else ⊤
            (qp < ratio x.1 x.2 → fstar n x = (x.2 + x.1 / (1 - M.c)) * ap n) ∧
            (qm ≤ ratio x.1 x.2 → ratio x.1 x.2 ≤ qp → fstar n x = x.2) ∧
            (ratio x.1 x.2 < qm → fstar n x = (x.1 + (1 + M.c) * x.2) * am n)) ∧
          M.IsAdmissible 0 fstar ∧
          ∀ x ∈ Estate, M.Vpi fstar 0 x.1 x.2 = M.V 0 x.1 x.2) := by sorry

end MDPFinance.MeanVariance
