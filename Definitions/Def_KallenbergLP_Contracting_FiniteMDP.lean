import Mathlib

namespace KallenbergLP.Contracting

/-! The finite, possibly terminating decision model of Kallenberg, §2.2. -/

variable (E : Type) [Fintype E] (A : E → Type) [∀ i, Fintype (A i)]

/-- A history at the beginning of period `n + 1`. Its first `n` entries are
state–action pairs, and its second component is the current state. -/
abbrev History (n : ℕ) := (Fin n → Σ i : E, A i) × E

/-- A randomized decision rule may depend on the entire history. -/
abbrev Policy := ∀ n : ℕ, (h : History E A n) → A h.2 → ℝ

/-- A stationary randomized decision rule. -/
abbrev StationaryRule := ∀ i : E, A i → ℝ

/-- A pure stationary decision rule. -/
abbrev PureRule := ∀ i : E, A i

/-- The model allows termination after a transition: rows need only sum to at most one. -/
structure FiniteMDP where
  transition : ∀ i : E, A i → E → ℝ
  reward : ∀ i : E, A i → ℝ
  transition_nonneg : ∀ i a j, 0 ≤ transition i a j
  transition_substochastic : ∀ i a, (∑ j, transition i a j) ≤ 1

variable {E A}

/-- A valid probability distribution over actions for every possible history. -/
def IsPolicy (π : Policy E A) : Prop :=
  (∀ n h a, 0 ≤ π n h a) ∧
  (∀ n h, ∑ a, π n h a = 1)

def IsStationaryRule (q : StationaryRule E A) : Prop :=
  (∀ i a, 0 ≤ q i a) ∧ (∀ i, ∑ a, q i a = 1)

def stationaryPolicy (q : StationaryRule E A) : Policy E A :=
  fun _ h a => q h.2 a

noncomputable def pureRule (f : PureRule E A) : StationaryRule E A := by
  classical
  exact fun i a => if a = f i then 1 else 0

noncomputable def purePolicy (f : PureRule E A) :
    Policy E A := stationaryPolicy (pureRule f)

/-- A policy is Markov when its decision rule depends on time and current state only. -/
def IsMarkov (π : Policy E A) : Prop :=
  ∃ q : ℕ → StationaryRule E A, ∀ n h a, π n h a = q n h.2 a

namespace FiniteMDP

variable (M : FiniteMDP E A)

/-- Probability of a complete history from initial state `i`. The stage index is
zero based in Lean, so stage `n` represents the book's time `t = n + 1`. -/
noncomputable def historyProbability (π : Policy E A) (i : E) :
    ∀ n : ℕ, History E A n → ℝ
  | 0, h => by
      classical
      exact if h.2 = i then 1 else 0
  | n + 1, h => by
      let previous : History E A n :=
        (fun k => h.1 (Fin.castSucc k), (h.1 (Fin.last n)).1)
      exact historyProbability π i n previous *
        π n previous (h.1 (Fin.last n)).2 *
        M.transition previous.2 (h.1 (Fin.last n)).2 h.2

/-- `P_R(X_t=j,Y_t=a | X₁=i)` with `t = n + 1`. -/
noncomputable def stateActionProbability (π : Policy E A) (i j : E)
    (a : A j) (n : ℕ) : ℝ :=
  ∑ actions : Fin n → Σ k : E, A k,
    M.historyProbability π i n (actions, j) * π n (actions, j) a

/-- The total expected reward for each initial state, expressed as the
absolutely convergent series guaranteed by contraction. -/
noncomputable def totalReward (π : Policy E A) (i : E) : ℝ :=
  ∑' n : ℕ, ∑ j : E, ∑ a : A j,
    M.stateActionProbability π i j a n * M.reward j a

/-- The state–action frequency vector (3.3.12), now for any policy. -/
noncomputable def frequency (β : E → ℝ) (π : Policy E A) :
    StationaryRule E A :=
  fun j a => ∑' n : ℕ, ∑ i : E, β i * M.stateActionProbability π i j a n

end FiniteMDP

end KallenbergLP.Contracting
