import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return

namespace NegativeDP.Switching

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

/-- Strauch §3 (p. 874), negative case: non-empty Borel `S`, `A`; law of motion `q ∈ Q(S | SA)`;
return `r ∈ M(SAS)` with `r > −∞` (real-valued, non-positive) and `qr > −∞` (integrable at every
state-action pair); `β = 1`. -/
structure Problem (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] where
  q : Kernel (S × A) S
  q_markov : IsMarkovKernel q
  r : S × A × S → ℝ
  r_measurable : Measurable r
  r_nonpos : ∀ x, r x ≤ 0
  qr_finite : ∀ s a, Integrable (fun t => r (s, a, t)) (q (s, a))

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- `M(X)`, negative case (p. 873): non-positive extended-real Baire functions. -/
def IsNegM {X : Type*} [MeasurableSpace X] (u : X → EReal) : Prop :=
  Measurable u ∧ ∀ x, u x ≤ 0

/-- The empty history `(s)` at the first decision: the paper's `H_1 = S`. -/
def Hist.start (s : S) : Hist S A 0 := ((fun i : Fin 0 => Fin.elim0 i), s)

/-- Extend a history `h = (s_1, a_1, …, s_n)` by the action `a` taken at its current state and
the next state `t`: `(s_1, a_1, …, s_n, a, t)`. -/
def Hist.snoc {n : ℕ} (h : Hist S A n) (a : A) (t : S) : Hist S A (n + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
    ((h.2, a), h.1), t)

/-- The transition kernel from a history and the chosen action to the next state. -/
noncomputable def nextKernel (P : Problem S A) (n : ℕ) : Kernel (Hist S A n × A) S :=
  P.q ∘ₖ Kernel.deterministic (fun ha : Hist S A n × A => (ha.1.2, ha.2)) (by fun_prop)

/-- One stage of the process under the plan `σ` at Lean decision `n`: from a history
`h ∈ Hist S A n`, draw `a ~ σ.κ n h`, then `t ~ q(· | h.2, a)`, and return `Hist.snoc h a t`. -/
noncomputable def stepKernel (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ) :
    Kernel (Hist S A n) (Hist S A (n + 1)) :=
  letI : IsMarkovKernel (σ.κ n) := σ.κ_markov n
  letI : IsMarkovKernel P.q := P.q_markov
  Kernel.map ((Kernel.id ×ₖ σ.κ n) ⊗ₖ (nextKernel P n).comap Prod.snd measurable_snd)
    (fun x : (Hist S A n × A) × S =>
      (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
        ((x.1.1.2, x.1.2), x.1.1.1), x.2) : Hist S A (n + 1)))

/-- Continuation law: started from a history `h ∈ Hist S A n` (Lean decision `n`, the paper's
stage `n + 1`) and using `σ`'s own kernels `σ.κ n, σ.κ (n+1), …` fed the full history, the law of
the history `k` stages later. -/
noncomputable def contKernel (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ) :
    (k : ℕ) → Kernel (Hist S A n) (Hist S A (n + k))
  | 0 => Kernel.id
  | k + 1 => stepKernel P σ (n + k) ∘ₖ contKernel P σ n k

/-- Expected one-stage loss `−σ_n q r` at a history `h ∈ Hist S A n`: the expectation of
`−r(s_n, a, t)` under `a ~ σ.κ n h`, `t ~ q(· | s_n, a)`, a value in `[0, ∞]`. -/
noncomputable def stepLoss (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) ∂P.q (h.2, a) ∂σ.κ n h

/-- Continuation return (p. 888): `u_n(s_1, a_1, …, s_n) = Σ_{j ≥ n} σ_n q ⋯ σ_j q r` (β = 1),
the expected total return from history `h ∈ Hist S A n` on when `σ`'s kernels are used from
Lean decision `n` on. A value in `[−∞, 0]`. -/
noncomputable def contReturn (P : Problem S A) (σ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : EReal :=
  -((∑' k : ℕ, ∫⁻ h', stepLoss P σ (n + k) h' ∂contKernel P σ n k h : ℝ≥0∞) : EReal)

/-- Law of the history before the paper's `(n+1)`st action from the initial state `s`
(Blackwell's recursion, with the negative problem's law of motion). -/
noncomputable def historyLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    (n : ℕ) → Measure (Hist S A n)
  | 0 => Measure.dirac (Hist.start s)
  | n + 1 => (historyLaw P π s n).bind (stepKernel P π n)

/-- Expected loss `−E r` at Lean stage `n` (the paper's stage `n + 1`), in `[0, ∞]`. -/
noncomputable def stageLoss (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ h, stepLoss P π n h ∂historyLaw P π s n

/-- `I(π)(s) = Σ_n π_1 q ⋯ π_n q r` (p. 875), a value in `[−∞, 0]`. -/
noncomputable def I (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : EReal :=
  -((∑' n, stageLoss P π s n : ℝ≥0∞) : EReal)

/-- `I_n(π, v)(s)` (p. 875): `n` stages, then the terminal reward `v(s_{n+1})`, `v ∈ M(S)`. -/
noncomputable def In (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (v : S → EReal)
    (s : S) : EReal :=
  -(((∑ j ∈ Finset.range n, stageLoss P π s j) +
      ∫⁻ h, (-(v h.2)).toENNReal ∂historyLaw P π s n : ℝ≥0∞) : EReal)

/-- `I_n(π, w_{n+1})` (p. 888): `n` stages, then the history-dependent terminal reward
`w_{n+1}(s_1, a_1, …, s_{n+1})`, `w ∈ M(SA⋯AS)` with `2n + 1` factors, i.e. on `Hist S A n`. -/
noncomputable def InH (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ)
    (w : Hist S A n → EReal) (s : S) : EReal :=
  -(((∑ j ∈ Finset.range n, stageLoss P π s j) +
      ∫⁻ h, (-(w h)).toENNReal ∂historyLaw P π s n : ℝ≥0∞) : EReal)

/-- The one-step operator `π_n(r + β w)` with `β = 1` (proof of Theorem 9.3, p. 888): at a history
`h ∈ Hist S A n`, the expectation of `r(s_n, a, t) + w(h, a, t)` under `a ~ π.κ n h`,
`t ~ q(· | s_n, a)`, computed as minus the integral of the loss (`w ≤ 0` is assumed wherever this
is used). -/
noncomputable def stepOp (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ)
    (w : Hist S A (n + 1) → EReal) (h : Hist S A n) : EReal :=
  -((∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + (-(w (Hist.snoc h a t))).toENNReal
      ∂P.q (h.2, a) ∂π.κ n h : ℝ≥0∞) : EReal)

/-- The switching policy of Theorem 9.3 (p. 888): at Lean decision `n` (the paper's stage `n+1`),
`π` uses `σ`'s kernel on `B = {u > v}` (σ's continuation return strictly larger than τ's) and
`τ`'s kernel on the complement. -/
def IsSwitch (P : Problem S A) (σ τ π : Plan (S := S) (A := A)) : Prop :=
  ∀ n (h : Hist S A n),
    π.κ n h = if contReturn P τ n h < contReturn P σ n h then σ.κ n h else τ.κ n h

/-- `w_n = max(u_n, v_n)` (proof of Theorem 9.3, p. 888), at Lean decision `n`. -/
noncomputable def wmax (P : Problem S A) (σ τ : Plan (S := S) (A := A)) (n : ℕ)
    (h : Hist S A n) : EReal :=
  max (contReturn P σ n h) (contReturn P τ n h)

/-- `ⁿπ` (p. 874) for a Markov plan: the plan it defines from the `(n+1)`st stage on. -/
def shift (π : MarkovPlan S A) (n : ℕ) : MarkovPlan S A := fun k => π (k + n)

/-- Drop the first state-action pair of a history. -/
def Hist.tail {n : ℕ} (h : Hist S A (n + 1)) : Hist S A n := (fun i => h.1 i.succ, h.2)

omit [StandardBorelSpace S] [Nonempty S] [StandardBorelSpace A] [Nonempty A] in
lemma Hist.measurable_tail (n : ℕ) : Measurable (Hist.tail (S := S) (A := A) (n := n)) := by
  unfold Hist.tail
  refine Measurable.prodMk ?_ measurable_snd
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_fst)

/-- `(f, π)` (p. 879): use the rule `f` at the first stage, then run `π` on the history from
the second state on. -/
noncomputable def prefixPlan (f : {g : S → A // Measurable g}) (π : Plan (S := S) (A := A)) :
    Plan (S := S) (A := A) where
  κ
    | 0 => Kernel.deterministic (fun h : Hist S A 0 => f.1 h.2) (f.2.comp measurable_snd)
    | k + 1 => (π.κ k).comap Hist.tail (Hist.measurable_tail k)
  κ_markov
    | 0 => by infer_instance
    | k + 1 => by
        have := π.κ_markov k
        infer_instance

end NegativeDP.Switching
