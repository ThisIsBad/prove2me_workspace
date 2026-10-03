import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Markov policy sequence `π : ℕ → ℝ × ℝ → ℝ` (post-transaction stock holding, as a function
of `(x0,x1)`) is admissible over `[n,N)` if `π k (x0,x1) ∈ Arange x0 x1` for every `n ≤ k < N`
and every state `(x0,x1) ∈ E = ℝ_{\ge0}²`, and `π k` is measurable. -/
def TransactionCostMarket.IsAdmissible (M : TransactionCostMarket Ω) (n : ℕ)
    (π : ℕ → ℝ × ℝ → ℝ) : Prop :=
  ∀ k, n ≤ k → k < M.N → (∀ x ∈ Estate, π k x ∈ M.Arange x.1 x.2) ∧ Measurable (π k)

/-- The terminal holdings `(X⁰,X¹)` reached after `k` steps from time `n`, state `(x0,x1)`,
under `π`, on path `ω`. -/
noncomputable def TransactionCostMarket.terminalState (M : TransactionCostMarket Ω)
    (π : ℕ → ℝ × ℝ → ℝ) :
    (k : ℕ) → (n : ℕ) → (x0 x1 : ℝ) → (ω : Ω) → ℝ × ℝ
  | 0, _, x0, x1, _ => (x0, x1)
  | (k + 1), n, x0, x1, ω =>
      let a := π n (x0, x1)
      M.terminalState π k (n + 1) (M.h x0 x1 a * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω) ω

/-- The value `V_n^π(x0,x1) := 𝔼[U(X⁰_N+X¹_N)]` of Markov strategy `π` from time `n`, state
`(x0,x1)`. -/
noncomputable def TransactionCostMarket.Vpi (M : TransactionCostMarket Ω) (π : ℕ → ℝ × ℝ → ℝ)
    (n : ℕ) (x0 x1 : ℝ) : ℝ :=
  ∫ ω, (fun p => M.U (p.1 + p.2)) (M.terminalState π (M.N - n) n x0 x1 ω) ∂M.measIP

/-- The value function `V_n(x0,x1) := sup_π V_n^π(x0,x1)` over admissible Markov strategies. -/
noncomputable def TransactionCostMarket.V (M : TransactionCostMarket Ω) (n : ℕ) (x0 x1 : ℝ) :
    ℝ :=
  ⨆ π ∈ {π : ℕ → ℝ × ℝ → ℝ | M.IsAdmissible n π}, M.Vpi π n x0 x1

end MDPFinance.MeanVariance
