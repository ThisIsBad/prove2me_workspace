import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- Auxiliary accumulator for the expected reward-to-go under a fixed policy `π`
(Bäuerle–Rieder, p. 18, PDF 33, unnumbered display defining `V_n^π`): starting at time `n` in
state `x` with reward already accrued `acc`, and running for `k` more stages toward a terminal
payoff `term`, `EFromToAcc M π term k n x acc` computes
`acc + 𝔼^π_{n,x}[Σ_{j=0}^{k-1} r_{n+j}(X_{n+j}, f_{n+j}(X_{n+j})) + term(X_{n+k})]`.
The accumulator carries the reward-so-far *outside* every integral rather than folding it into a
recursively-defined value (which would make `Theorem 2.3.4`'s recursion true by unfolding): the
accumulator is only consumed once, at `k = 0`, so recovering the one-step recursion for
`k = m - n` requires the (short but genuine) fact that the accumulator enters linearly. -/
noncomputable def EFromToAcc (M : MarkovDecisionModel E A N) (π : Policy M) (term : E → EReal) :
    (k : ℕ) → (n : ℕ) → (x : E) → (acc : EReal) → EReal
  | 0, _, x, acc => acc + term x
  | (k + 1), n, x, acc =>
      erealIntegral (M.Q n (x, π.1 n x))
        (fun x' => EFromToAcc M π term k (n + 1) x' (acc + (M.r n (x, π.1 n x) : EReal)))

/-- The expected reward-to-go `𝔼^π_{n,x}[Σ_{k=n}^{m-1} r_k(X_k, f_k(X_k)) + term(X_m)]` under a
fixed policy `π`, from time `n` to time `m ≥ n`, with terminal payoff `term` at time `m`. -/
noncomputable def EFromTo (M : MarkovDecisionModel E A N) (π : Policy M) (n m : ℕ) (x : E)
    (term : E → EReal) : EReal :=
  EFromToAcc M π term (m - n) n x 0

/-- The value `V_n^π(x)` of policy `π` from time `n` in state `x` (Bäuerle–Rieder, p. 18, PDF 33,
unnumbered display): `V_n^π(x) := 𝔼^π_{n,x}[Σ_{k=n}^{N-1} r_k(X_k,f_k(X_k)) + g_N(X_N)]`. -/
noncomputable def Vpi (M : MarkovDecisionModel E A N) (π : Policy M) (n : ℕ) (x : E) : EReal :=
  EFromTo M π n N x (fun x => (M.g x : EReal))

/-- The value function `V_n(x) := sup_π V_n^π(x)` (Bäuerle–Rieder, p. 18, PDF 33, unnumbered
display), the maximal expected total reward from time `n` in state `x`. -/
noncomputable def V (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : EReal :=
  ⨆ π : Policy M, Vpi M π n x

/-- Auxiliary for Theorem 2.3.8b: `T_n T_{n+1} ⋯ T_{n+k-1}` applied to a terminal function,
i.e. `k` applications of the maximal-reward operator starting at time `n`, innermost first. -/
noncomputable def TChain (M : MarkovDecisionModel E A N) : (k : ℕ) → (n : ℕ) → (E → EReal) →
    (E → EReal)
  | 0, _, v => v
  | (k + 1), n, v => T M n (TChain M k (n + 1) v)

/-- Auxiliary for Theorem 2.3.4b: `T_n^{f_n} T_{n+1}^{f_{n+1}} ⋯ T_{n+k-1}^{f_{n+k-1}}` applied to
a terminal function, under a fixed policy `π`. -/
noncomputable def TfChain (M : MarkovDecisionModel E A N) (π : Policy M) : (k : ℕ) → (n : ℕ) →
    (E → EReal) → (E → EReal)
  | 0, _, v => v
  | (k + 1), n, v => Tf M n (TfChain M π k (n + 1) v) (π.1 n)

/-- The one-step transition kernel of the state process under a fixed policy `π` at time `n`:
`Q_n(·|x, f_n(x))`, pulled back along `x ↦ (x, f_n(x))`. -/
noncomputable def oneStepKernel (M : MarkovDecisionModel E A N) (π : Policy M) (n : ℕ) :
    Kernel E E :=
  (M.Q n).comap (fun x => (x, π.1 n x)) ((measurable_id.prodMk (π.2.1 n)))

/-- The `k`-step transition kernel of the state process under `π`, starting at time `n`: the law
of `X_{n+k}` given `X_n`. Used to state Theorem 2.3.12's `ℙ^{π}_{n,x}`-almost-sure conclusion
without constructing the full canonical path measure on `Ω = E^{N+1}`. -/
noncomputable def stepKernelAux (M : MarkovDecisionModel E A N) (π : Policy M) : (k : ℕ) →
    (n : ℕ) → Kernel E E
  | 0, _ => Kernel.id
  | (k + 1), n => Kernel.comp (stepKernelAux M π k (n + 1)) (oneStepKernel M π n)

/-- `stepKernel M π n m`: the law of `X_m` given `X_n = x` under policy `π`, for `n ≤ m`. -/
noncomputable def stepKernel (M : MarkovDecisionModel E A N) (π : Policy M) (n m : ℕ) :
    Kernel E E :=
  stepKernelAux M π (m - n) n

/-- The model with the one-stage and terminal rewards replaced by their positive parts `r_n^+`,
`g_N^+` (same `D_n`, `Q_n`), used to state the Integrability Assumption (AN). -/
noncomputable def MarkovDecisionModel.posPart (M : MarkovDecisionModel E A N) :
    MarkovDecisionModel E A N :=
  { M with
    r := fun n xa => max (M.r n xa) 0
    hr_meas := fun n hn => (M.hr_meas n hn).max measurable_const
    g := fun x => max (M.g x) 0
    hg_meas := M.hg_meas.max measurable_const }

/-- `δ_n^N(x) := sup_π 𝔼^π_{n,x}[Σ_{k=n}^{N-1} r_k^+(X_k, f_k(X_k)) + g_N^+(X_N)]` (Bäuerle–Rieder,
p. 17, PDF 32): the maximal expected total *positive* reward from `(n,x)`. -/
noncomputable def deltaN (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : EReal :=
  ⨆ π : Policy M, EFromTo M.posPart ⟨π.1, π.2⟩ n N x (fun x => ((max (M.g x) 0 : ℝ) : EReal))

/-- The Integrability Assumption (AN) (Bäuerle–Rieder, p. 17, PDF 32): `δ_n^N(x) < ∞` for all
`n = 0, …, N` and `x ∈ E`. The book assumes (AN) "for the N-stage Markov Decision Problems
throughout the following chapters"; it is what makes every expectation `V_n^π(x)` well defined
and keeps `V_n^π`, `V_n` in `[-∞, ∞)`. -/
def IntegrabilityAssumption (M : MarkovDecisionModel E A N) : Prop :=
  ∀ n ≤ N, ∀ x, deltaN M n x < ⊤

end MDPFinance.Bellman
