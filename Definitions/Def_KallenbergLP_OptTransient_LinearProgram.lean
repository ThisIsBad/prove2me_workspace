import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_Policy

namespace KallenbergLP.OptTransient

/-- Stationary rules are probability distributions supported on the available actions. -/
def IsStationaryRule {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α) : Prop :=
  ∀ i, (∀ a, 0 ≤ π i a) ∧
    (∀ a, a ∉ m.actions i → π i a = 0) ∧
    (∑ a ∈ m.actions i, π i a) = 1

/-- State transition matrix under a stationary rule, P(π). -/
noncomputable def transitionMatrix {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ a ∈ m.actions i, m.transition i a j * π i a

/-- Formula (3.3.11): the occupancy associated with a transient stationary rule. -/
noncomputable def stationaryOccupation {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (π : StationaryRule n α) (s : StateAction m) : ℝ :=
  (∑ i : Fin n, β i * ((1 - transitionMatrix m π)⁻¹) i s.1) * π s.1 s.2.1

/-- The state mass xᵢ = ∑ₐ xᵢₐ. -/
noncomputable def stateMass {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (x : StateAction m → ℝ) (i : Fin n) : ℝ :=
  ∑ a : {a : α // a ∈ m.actions i}, x ⟨i, a⟩

/-- Formula (3.3.8), with a default zero outside the feasible action set. -/
noncomputable def ruleOfOccupation {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (x : StateAction m → ℝ) : StationaryRule n α :=
  fun i a => if h : a ∈ m.actions i then x ⟨i, ⟨a, h⟩⟩ / stateMass m x i else 0

/-- The equality-constrained feasible set of the dual LP (3.3.7). -/
def IsFeasible {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (x : StateAction m → ℝ) : Prop :=
  (∀ s, 0 ≤ x s) ∧
  (∀ j : Fin n, (∑ s : StateAction m,
    ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) * x s) = β j)

/-- The feasible polyhedron P of (3.3.7). -/
def feasibleSet {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) : Set (StateAction m → ℝ) :=
  {x | IsFeasible m β x}

/-- Objective of (3.3.7). -/
noncomputable def objective {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (x : StateAction m → ℝ) : ℝ :=
  ∑ s : StateAction m, m.reward s.1 s.2.1 * x s

/-- An optimal solution of the equality-constrained LP (3.3.7). -/
def IsOptimalLP {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (x : StateAction m → ℝ) : Prop :=
  IsFeasible m β x ∧ ∀ y, IsFeasible m β y → objective m y ≤ objective m x

/-- A stationary rule is pure when exactly one available action has probability one in each state. -/
def IsPureRule {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α) : Prop :=
  ∃ f : (i : Fin n) → {a : α // a ∈ m.actions i},
    ∀ i a, π i a = if a = (f i).1 then 1 else 0

/-- The set of total rewards of transient policies from initial state `i`. -/
def transientValues {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (i : Fin n) : Set ℝ :=
  {v | ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R ∧ v = totalReward m R i}

/-- Equation (3.3.2), used only when the transient value is bounded above. -/
noncomputable def optimalValue {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (i : Fin n) : ℝ :=
  sSup (transientValues m i)

/-- Definition 3.3.1: a TMD-superharmonic vector. -/
def IsSuperharmonic {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (w : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∀ a : {a : α // a ∈ m.actions i},
    m.reward i a.1 + ∑ j, m.transition i a.1 j * w j ≤ w i

/-- Optimality among all transient history-dependent randomized policies, componentwise in i. -/
def IsOptimalTransient {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (R : Policy n α) : Prop :=
  IsPolicy m R ∧ IsTransient m R ∧
  ∀ S : Policy n α, IsPolicy m S → IsTransient m S →
    ∀ i : Fin n, totalReward m S i ≤ totalReward m R i

/-- Notation 3.3.1: occupation vectors from all transient policies. -/
def K {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) : Set (StateAction m → ℝ) :=
  {x | ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R ∧ occupation m β R = x}

/-- Occupation vectors from transient Markov policies. -/
def KMarkov {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) : Set (StateAction m → ℝ) :=
  {x | ∃ R : Policy n α, IsPolicy m R ∧ IsMarkov R ∧
    IsTransient m R ∧ occupation m β R = x}

/-- Occupation vectors from transient stationary policies. -/
def KStationary {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) : Set (StateAction m → ℝ) :=
  {x | ∃ R : Policy n α, IsPolicy m R ∧ IsStationary R ∧
    IsTransient m R ∧ occupation m β R = x}

/-- Occupation vectors from transient pure stationary policies. -/
def KPure {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) : Set (StateAction m → ℝ) :=
  {x | ∃ f : (i : Fin n) → {a : α // a ∈ m.actions i},
    IsTransient m (purePolicy (fun i => (f i).1)) ∧
    occupation m β (purePolicy (fun i => (f i).1)) = x}

end KallenbergLP.OptTransient
