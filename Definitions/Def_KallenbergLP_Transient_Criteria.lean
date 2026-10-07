import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- The maximal probability of surviving `t` transitions in the model of Lemma 3.2.2. -/
def survivalIterate (M : MDP N α) : ℕ → Fin N → ℝ
  | 0, _ => 1
  | t + 1, i =>
      (M.actions i).sup' (M.actions_nonempty i) fun a =>
        ∑ j : Fin N, M.transition i a j * survivalIterate M t j

/-- Probability that the process is still in the original state space at epoch `t + 1`. -/
def survivalProb (M : MDP N α) (R : Policy M) (i : Fin N) (t : ℕ) : ℝ :=
  ∑ j : Fin N, stateProb M R i j t

/-- A contracting finite dynamic programming model, as on p. 23. -/
def Contracting (M : MDP N α) : Prop :=
  ∃ (μ : Fin N → ℝ) (c : ℝ),
    (∀ i, 0 < μ i) ∧ 0 ≤ c ∧ c < 1 ∧
      ∀ i a, a ∈ M.actions i →
        (∑ j : Fin N, M.transition i a j * μ j) ≤ c * μ i

/-- Feasible points of the state-action LP in Theorem 3.2.4(v). -/
def LPFeasible (M : MDP N α) (β : Fin N → ℝ)
    (x : Fin N → α → ℝ) : Prop :=
  (∀ i a, a ∈ M.actions i → 0 ≤ x i a) ∧
  (∀ j, (∑ i : Fin N, ∑ a ∈ M.actions i,
      ((if i = j then (1 : ℝ) else 0) - M.transition i a j) * x i a) ≤ β j)

def LPObjective (M : MDP N α) (x : Fin N → α → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ a ∈ M.actions i, x i a

/-- The LP has an attained finite optimum, as in Definition 1.3.2 and Theorem 3.2.4(v). -/
def LPFinite (M : MDP N α) (β : Fin N → ℝ) : Prop :=
  ∃ x : Fin N → α → ℝ,
    LPFeasible M β x ∧
      ∀ y : Fin N → α → ℝ, LPFeasible M β y → LPObjective M y ≤ LPObjective M x

/-- The first `t` decisions are `f_t, f_(t-1), ..., f_1`; later decisions use `f_1`. -/
def backwardPolicy (M : MDP N α) (f : ℕ → PureRule M) (t : ℕ) : Policy M where
  choose := fun n h a =>
    (purePolicy M (f (if n < t then t - n else 1))).choose n h a
  choose_nonneg := by
    intro n h a
    exact (purePolicy M (f (if n < t then t - n else 1))).choose_nonneg n h a
  choose_outside := by
    intro n h a ha
    exact (purePolicy M (f (if n < t then t - n else 1))).choose_outside n h a ha
  choose_sum_one := by
    intro n h
    exact (purePolicy M (f (if n < t then t - n else 1))).choose_sum_one n h

def extremalPolicy (M : MDP N α) (f : ℕ → PureRule M)
    (R₀ : Policy M) (t : ℕ) : Policy M :=
  if t = 0 then R₀ else backwardPolicy M f t

end KallenbergLP.Transient
