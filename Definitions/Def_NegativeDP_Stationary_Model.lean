import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return

namespace NegativeDP.Stationary

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

/-- Strauch's dynamic programming problem in the negative case (§3, p. 874): non-empty Borel
state and action sets `S`, `A`; a law of motion `q ∈ Q(S | SA)`; a return function
`r ∈ M(SAS)` with `r > −∞` (real valued) and `qr > −∞` (integrable at every `(s, a)`);
in the negative case `r ≤ 0` and `β = 1`. -/
structure Problem (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] where
  q : Kernel (S × A) S
  q_markov : IsMarkovKernel q
  r : S × A × S → ℝ
  r_measurable : Measurable r
  r_nonpos : ∀ x, r x ≤ 0
  qr_finite : ∀ s a, Integrable (fun t => r (s, a, t)) (q (s, a))

/-- `M(X)` in the negative case (p. 873): non-positive, extended-real valued Baire (Borel
measurable) functions on `X`. -/
def IsNegM {X : Type*} [MeasurableSpace X] (u : X → EReal) : Prop :=
  Measurable u ∧ ∀ x, u x ≤ 0

/-- `qu(x) = ∫ u(x, y) dq(y | x)` (p. 873) for `u ∈ M(XY)`, computed as `−∫ (−u)` so that
the value `−∞` is kept. -/
noncomputable def kint {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : Kernel X Y) [IsMarkovKernel q] (u : X × Y → EReal) (x : X) : EReal :=
  -(((∫⁻ y, (-(u (x, y))).toENNReal ∂q x : ℝ≥0∞)) : EReal)

/-- `pu = ∫ u dp` for `u ≤ 0` and a measure `p` on `S`, computed as `−∫ (−u) dp`. -/
noncomputable def pInt {X : Type*} [MeasurableSpace X] (p : Measure X)
    [IsProbabilityMeasure p] (u : X → EReal) :
    EReal :=
  -(((∫⁻ x, (-(u x)).toENNReal ∂p : ℝ≥0∞)) : EReal)

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

set_option linter.unusedSectionVars false

/-! ### Histories and policy constructions -/

/-- The initial state `s₁` of a history. -/
def Hist.init : {n : ℕ} → Hist S A n → S
  | 0, h => h.2
  | _ + 1, h => (h.1 0).1

theorem Hist.measurable_init (n : ℕ) : Measurable (Hist.init (S := S) (A := A) (n := n)) := by
  cases n with
  | zero => exact measurable_snd
  | succ n =>
    exact (measurable_fst.comp (measurable_pi_apply (0 : Fin (n + 1)))).comp
      (measurable_fst (α := Fin (n + 1) → S × A) (β := S))

/-- Drop the first state-action pair of a history: the history seen from the second stage on. -/
def Hist.tail {n : ℕ} (h : Hist S A (n + 1)) : Hist S A n := (fun i => h.1 i.succ, h.2)

theorem Hist.measurable_tail (n : ℕ) : Measurable (Hist.tail (S := S) (A := A) (n := n)) := by
  unfold Hist.tail
  refine Measurable.prodMk ?_ measurable_snd
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_fst)

/-- `π^nσ = {π₁, …, πₙ, σₙ₊₁, …}` (p. 874): follow `π` for `n` stages, then `σ`.
Lean decisions are numbered from `0`, so decisions `0, …, n-1` come from `π`. -/
noncomputable def switchAt (π : Plan (S := S) (A := A)) (n : ℕ) (σ : Plan (S := S) (A := A)) :
    Plan (S := S) (A := A) where
  κ k := if k < n then π.κ k else σ.κ k
  κ_markov k := by
    by_cases hk : k < n
    · simp only [hk, if_true]; exact π.κ_markov k
    · simp only [hk, if_false]; exact σ.κ_markov k

/-- `(f, π) = (f, π₁, π₂, …)` (p. 879): use the rule `f` at the first stage, then run `π`
on the history from the second state on. -/
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

/-- The random semi-Markov plan whose `n`th decision draws the action from `κ' n (s₁, sₙ)`. -/
noncomputable def semiMarkovPlan (κ' : ℕ → Kernel (S × S) A)
    (hκ' : ∀ n, IsMarkovKernel (κ' n)) : Plan (S := S) (A := A) where
  κ n := (κ' n).comap (fun h : Hist S A n => (Hist.init h, h.2))
    ((Hist.measurable_init n).prodMk measurable_snd)
  κ_markov n := by
    have := hκ' n
    infer_instance

/-- The random Markov plan whose `n`th decision draws the action from `κ'' n (sₙ)`. -/
noncomputable def randomMarkovPlan (κ'' : ℕ → Kernel S A)
    (hκ'' : ∀ n, IsMarkovKernel (κ'' n)) : Plan (S := S) (A := A) where
  κ n := (κ'' n).comap (fun h : Hist S A n => h.2) measurable_snd
  κ_markov n := by
    have := hκ'' n
    exact Kernel.IsMarkovKernel.comap (κ'' n) measurable_snd

/-- Non-random semi-Markov (p. 874): each `πₙ` is a degenerate element of `Q(A | SS)`, the
action depends measurably on the initial state, the current state and `n` only. -/
def IsSemiMarkov (π : Plan (S := S) (A := A)) : Prop :=
  ∃ g : ℕ → S × S → A, (∀ n, Measurable (g n)) ∧
    ∀ n (h : Hist S A n), π.κ n h = Measure.dirac (g n (Hist.init h, h.2))

/-- Random semi-Markov (p. 874): each `πₙ ∈ Q(A | SS)`. -/
def IsRandomSemiMarkov (π : Plan (S := S) (A := A)) : Prop :=
  ∃ κ' : ℕ → Kernel (S × S) A, (∀ n, IsMarkovKernel (κ' n)) ∧
    ∀ n (h : Hist S A n), π.κ n h = κ' n (Hist.init h, h.2)

/-- Random Markov (p. 874): each `πₙ ∈ Q(A | S)`. -/
def IsRandomMarkov (π : Plan (S := S) (A := A)) : Prop :=
  ∃ κ'' : ℕ → Kernel S A, (∀ n, IsMarkovKernel (κ'' n)) ∧
    ∀ n (h : Hist S A n), π.κ n h = κ'' n h.2

/-- Non-random Markov (p. 874): `π = {f₁, f₂, …}` with measurable `fₙ : S → A`. -/
def IsMarkov (π : Plan (S := S) (A := A)) : Prop :=
  ∃ m : MarkovPlan S A, π = m.toPlan

/-! ### Laws of the process and returns -/

/-- The transition kernel from a history and the chosen action to the next state. -/
noncomputable def nextKernel (P : Problem S A) (n : ℕ) : Kernel (Hist S A n × A) S :=
  P.q ∘ₖ Kernel.deterministic (fun ha : Hist S A n × A => (ha.1.2, ha.2)) (by fun_prop)

/-- The law of the history before the `(n+1)`-st decision (the paper's `H_{n+1}`), started
at the initial state `s`. -/
noncomputable def historyLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    (n : ℕ) → Measure (Hist S A n)
  | 0 => Measure.dirac ((fun i : Fin 0 => Fin.elim0 i), s)
  | n + 1 =>
      letI : IsMarkovKernel (π.κ n) := π.κ_markov n
      letI : IsMarkovKernel P.q := P.q_markov
      have happend : Measurable
          (fun x : (Hist S A n × A) × S =>
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A)
                (Fin.last n)).symm ((x.1.1.2, x.1.2), x.1.1.1), x.2)) := by
        fun_prop
      (Measure.compProd (Measure.compProd (historyLaw P π s n) (π.κ n))
        (nextKernel P n)).map
        (fun x =>
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A)
            (Fin.last n)).symm ((x.1.1.2, x.1.2), x.1.1.1), x.2))

/-- Law of (history, action, next state) at Lean stage `n` (the paper's stage `n+1`). -/
noncomputable def stageLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    Measure ((Hist S A n × A) × S) := by
  letI : IsMarkovKernel (π.κ n) := π.κ_markov n
  letI : IsMarkovKernel P.q := P.q_markov
  exact Measure.compProd (Measure.compProd (historyLaw P π s n) (π.κ n)) (nextKernel P n)

/-- Expectation, from the initial state `s`, of `u(sₙ, aₙ, sₙ₊₁)` at Lean stage `n`, for
`u ≤ 0`; computed as `−∫ (−u)` so that `−∞` is kept. -/
noncomputable def stageExp (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ)
    (u : S × A × S → EReal) : EReal :=
  -(((∫⁻ x, (-(u (x.1.1.2, x.1.2, x.2))).toENNReal ∂stageLaw P π s n : ℝ≥0∞)) : EReal)

/-- Expected loss `−E r` at Lean stage `n`, a value in `[0, ∞]`. -/
noncomputable def stageLoss (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) ∂stageLaw P π s n

/-- The expected total return `I(π)(s) = Σₙ π₁q ⋯ πₙqr` (p. 875), a value in `[−∞, 0]`. -/
noncomputable def I (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : EReal :=
  -(((∑' n, stageLoss P π s n : ℝ≥0∞)) : EReal)

/-- `Iₙ(π, v)(s)` (p. 875): the expected return over `n` stages plus the terminal reward
`v(sₙ₊₁)`, for `v ∈ M(S)`. -/
noncomputable def In (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (v : S → EReal)
    (s : S) : EReal :=
  -((((∑ j ∈ Finset.range n, stageLoss P π s j) +
      ∫⁻ h, (-(v h.2)).toENNReal ∂historyLaw P π s n : ℝ≥0∞)) : EReal)

/-- `v* = sup_π I(π)` (p. 883), the supremum over every randomized history-dependent plan. -/
noncomputable def vstar (P : Problem S A) (s : S) : EReal :=
  ⨆ π : Plan (S := S) (A := A), I P π s

/-- `π` is optimal (p. 875): `I(π) ≥ sup_σ I(σ)` at every state. -/
def IsOptimal (P : Problem S A) (π : Plan (S := S) (A := A)) : Prop :=
  ∀ s, vstar P s ≤ I P π s

/-- The operator `T` of a measurable rule `f` (p. 878), with `β = 1`:
`Tu(s) = ∫ r(s, f(s), t) + u(t) dq(t | s, f(s))`, computed as `−∫ (−r − u)`. -/
noncomputable def T (P : Problem S A) (f : {g : S → A // Measurable g}) (u : S → EReal)
    (s : S) : EReal :=
  -(((∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + (-(u t)).toENNReal
      ∂P.q (s, f.1 s) : ℝ≥0∞)) : EReal)

end NegativeDP.Stationary
