import Definitions.Def_KallenbergLP_Positive_Value

namespace KallenbergLP.Positive

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- Coordinates of the dual program are indexed only by admissible state-action pairs. -/
abbrev Flow (M : MDP N α) := (i : Fin N) → M.actions i → ℝ

/-- Notation 3.1.1: states with positive total flow. -/
def occupiedStates (M : MDP N α) (x : Flow M) : Set (Fin N) :=
  {i | 0 < ∑ a : M.actions i, x i a}

/-- Left side of (3.5.2) for the state `j`. -/
def dualBalance (M : MDP N α) (x : Flow M) (j : Fin N) : ℝ :=
  (∑ a : M.actions j, x j a) -
    ∑ i : Fin N, ∑ a : M.actions i, M.transition i a.val j * x i a

/-- The feasible region of (3.5.2), with its `≤ β_j` balance constraints. -/
def dualFeasible (M : MDP N α) (β : Fin N → ℝ) : Set (Flow M) :=
  {x | (∀ i (a : M.actions i), 0 ≤ x i a) ∧
    ∀ j, dualBalance M x j ≤ β j}

/-- Objective of (3.5.2). -/
def dualObjective (M : MDP N α) (x : Flow M) : ℝ :=
  ∑ i : Fin N, ∑ a : M.actions i, M.reward i a.val * x i a

/-- An optimal solution among all feasible dual flows. -/
def IsDualOptimal (M : MDP N α) (β : Fin N → ℝ) (x : Flow M) : Prop :=
  x ∈ dualFeasible M β ∧
    ∀ y ∈ dualFeasible M β, dualObjective M y ≤ dualObjective M x

end KallenbergLP.Positive
