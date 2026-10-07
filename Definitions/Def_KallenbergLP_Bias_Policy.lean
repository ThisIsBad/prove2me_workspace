import Definitions.Def_KallenbergLP_Bias_MDP

namespace KallenbergLP.Bias

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- A history at time `n + 1`: `n + 1` states and `n` earlier actions. -/
structure History (N : ℕ) (α : Type) (n : ℕ) where
  states : Fin (n + 1) → Fin N
  chosen : Fin n → α

instance (n : ℕ) : Fintype (History N α n) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (n + 1) → Fin N) × (Fin n → α))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun h => (h.states, h.chosen)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro h; cases h; rfl }

def History.last {n : ℕ} (h : History N α n) : Fin N := h.states ⟨n, by omega⟩

def History.prefix {n : ℕ} (h : History N α n) (k : Fin n) : History N α k.val where
  states := fun i => h.states ⟨i.val, by omega⟩
  chosen := fun i => h.chosen ⟨i.val, by omega⟩

/-- An admissible randomized decision rule at every finite history, hence a policy in C. -/
structure Policy (M : MDP N α) where
  choose : ∀ n, History N α n → α → ℝ
  choose_nonneg : ∀ n h a, 0 ≤ choose n h a
  choose_outside : ∀ n h a, a ∉ M.actions h.last → choose n h a = 0
  choose_sum_one : ∀ n h, (∑ a : α, choose n h a) = 1

/-- A selector of one admissible action in each state, representing C_D. -/
structure PureRule (M : MDP N α) where
  choose : Fin N → α
  admissible : ∀ i, choose i ∈ M.actions i

def purePolicy (M : MDP N α) (f : PureRule M) : Policy M where
  choose := fun _ h a => if a = f.choose h.last then 1 else 0
  choose_nonneg := by intros; split_ifs <;> norm_num
  choose_outside := by
    intro n h a ha
    have hne : a ≠ f.choose h.last := by
      intro heq
      exact ha (heq ▸ f.admissible h.last)
    simp [hne]
  choose_sum_one := by
    intro n h
    classical
    simp

/-- Probability of a complete history, conditional on the initial state. -/
def historyProb (M : MDP N α) (R : Policy M) (i : Fin N)
    (n : ℕ) (h : History N α n) : ℝ :=
  (if h.states ⟨0, by omega⟩ = i then 1 else 0) *
    ∏ k : Fin n,
      R.choose k.val (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k)
          (h.states ⟨k.val + 1, by omega⟩)

/-- Joint probability of state `j` and action `a` in period `n + 1`. -/
def occupancy (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α)
    (n : ℕ) : ℝ :=
  ∑ h : History N α n,
    if h.last = j then historyProb M R i n h * R.choose n h a else 0

end KallenbergLP.Bias
