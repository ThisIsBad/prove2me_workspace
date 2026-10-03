import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_OnePeriod

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- The multiperiod terminal wealth Markov Decision Model (Bäuerle–Rieder, p. 79-80, PDF 93-94):
state space `E := domU`, action space `A := ℝ^d`, transition `T_n(x,a,z) := (1+i_{n+1})(x+a·z)`,
`r_n ≡ 0`, `g_N := U`. Bundles the probability space, the interest rates (positive bond factors),
the relative risk process `R_1, …, R_N` of Section 3.1 — assumed independent, as at the start of
Section 4.2 — the standing no-arbitrage Assumption (FM)(i) (in its local form, Theorem 3.1.5),
and the utility function (Definition 3.4.1). -/
structure TerminalWealthMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  R : ℕ → Ω → (Fin d → ℝ)
  hR_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (R n)
  /-- `R_1, …, R_N` are independent (Section 4.2's standing assumption). -/
  hR_indep : iIndepFun (fun n : Fin N => R (n.val + 1)) measIP
  /-- Assumption (FM)(i): no arbitrage opportunities, in the local form of Theorem 3.1.5. -/
  hNA : ∀ n, 1 ≤ n → n ≤ N → NoArbitrageOnePeriod measIP (R n)
  domU : Set ℝ
  U : ℝ → ℝ
  hU_mono : StrictMonoOn U domU
  hU_concave : StrictConcaveOn ℝ domU U
  hU_cont : ContinuousOn U domU

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Assumption (FM)(ii) (Bäuerle–Rieder, p. 79, PDF 93): `𝔼‖R_n‖ < ∞` for `n = 1, …, N`. -/
def TerminalWealthMarket.FM2 (M : TerminalWealthMarket Ω d) : Prop :=
  ∀ n, 1 ≤ n → n ≤ M.N → Integrable (fun ω => ∑ k, |M.R n ω k|) M.measIP

/-- The bond price `S⁰_n := ∏_{k=1}^n (1+i_k)`, `S⁰_0 := 1` (Bäuerle–Rieder, p. 61, PDF 75). -/
noncomputable def TerminalWealthMarket.S0 (M : TerminalWealthMarket Ω d) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + M.i (k + 1))

/-- The admissible actions `D_n(x)` (Bäuerle–Rieder, Eq. (4.4), p. 80, PDF 94):
`D_n(x) := {a ∈ ℝ^d | (1+i_{n+1})(x + a·R_{n+1}) ∈ domU  ℙ-a.s.}`. -/
def TerminalWealthMarket.D (M : TerminalWealthMarket Ω d) (n : ℕ) (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ᵐ ω ∂M.measIP, (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k) ∈ M.domU}

/-- A Markov portfolio strategy `π : ℕ → ℝ → (Fin d → ℝ)` is admissible over `[n,N)` if `π k` is
measurable and `π k x ∈ D_k(x)` for every stage `n ≤ k < N` and every state `x ∈ E = domU`
(Bäuerle–Rieder, p. 80, PDF 94: a policy of the Markov Decision Model with state space `domU`). -/
def TerminalWealthMarket.IsAdmissible (M : TerminalWealthMarket Ω d) (n : ℕ)
    (π : ℕ → ℝ → (Fin d → ℝ)) : Prop :=
  ∀ k, n ≤ k → k < M.N → (∀ x ∈ M.domU, π k x ∈ M.D k x) ∧ Measurable (π k)

/-- The terminal wealth `X_{n+k}` reached after `k` steps from time `n`, state `x`, under a
Markov portfolio strategy `π`, on the sample path `ω` (Bäuerle–Rieder, p. 80, PDF 94, transition
function `T_n(x,a,z) = (1+i_{n+1})(x+a·z)`, iterated). -/
def TerminalWealthMarket.terminalWealth (M : TerminalWealthMarket Ω d)
    (π : ℕ → ℝ → (Fin d → ℝ)) : (k : ℕ) → (n : ℕ) → (x : ℝ) → (ω : Ω) → ℝ
  | 0, _, x, _ => x
  | (k + 1), n, x, ω =>
      M.terminalWealth π k (n + 1)
        ((1 + M.i (n + 1)) * (x + ∑ j, π n x j * M.R (n + 1) ω j)) ω

/-- The value `V_n^π(x) := 𝔼[U(X_N)] ∈ [-∞, ∞)` of Markov portfolio strategy `π` from time `n`,
state `x` (Bäuerle–Rieder, Eq. (4.6), p. 80, PDF 94). -/
noncomputable def TerminalWealthMarket.Vpi (M : TerminalWealthMarket Ω d)
    (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (x : ℝ) : EReal :=
  erealIntegral M.measIP (fun ω => (M.U (M.terminalWealth π (M.N - n) n x ω) : EReal))

/-- The value function `V_n(x) := sup_π V_n^π(x)`, the supremum over admissible Markov
portfolio strategies (Bäuerle–Rieder, Eq. (4.6), p. 80, PDF 94). -/
noncomputable def TerminalWealthMarket.V (M : TerminalWealthMarket Ω d) (n : ℕ) (x : ℝ) :
    EReal :=
  ⨆ π ∈ {π : ℕ → ℝ → (Fin d → ℝ) | M.IsAdmissible n π}, M.Vpi π n x

end MDPFinance.TerminalWealth
