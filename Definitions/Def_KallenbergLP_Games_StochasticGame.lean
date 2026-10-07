import Mathlib

namespace KallenbergLP.Games

/-- A two-person zero-sum stochastic game `(E, A, B, p, r)` of §6.1 (pp. 186–187), with state space
`E = Fin N` with `N > 0`. `A i` and `B i` are the finite, nonempty action sets of player I and player II in
state `i`, inside the finite action spaces `α` and `β`. In state `i`, if player I chooses
`a ∈ A i` and player II chooses `b ∈ B i`, player I receives `r i a b` from player II and the
next state is `j` with probability `p i a b j`, where `p i a b j ≥ 0` and `∑ j, p i a b j ≤ 1`.
Values of `p` and `r` outside the action sets are never used. -/
structure Game (N : ℕ) (α β : Type) where
  N_pos : 0 < N
  A : Fin N → Finset α
  B : Fin N → Finset β
  p : Fin N → α → β → Fin N → ℝ
  r : Fin N → α → β → ℝ
  A_nonempty : ∀ i, (A i).Nonempty
  B_nonempty : ∀ i, (B i).Nonempty
  p_nonneg : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, ∀ j, 0 ≤ p i a b j
  p_sum_le_one : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, ∑ j, p i a b j ≤ 1

variable {N : ℕ} {α β : Type} [Fintype α] [Fintype β]

/-- A history at time `n + 1` (an element of `H_{n+1}`, p. 186): the states
`i_1, …, i_{n+1}` and the actions `a_1, …, a_n` of player I and `b_1, …, b_n` of player II.
Index `k : Fin (n + 1)` stands for time `k + 1`. -/
structure History (N : ℕ) (α β : Type) (n : ℕ) where
  states : Fin (n + 1) → Fin N
  act1 : Fin n → α
  act2 : Fin n → β

instance (n : ℕ) : Fintype (History N α β n) :=
  Fintype.ofEquiv ((Fin (n + 1) → Fin N) × (Fin n → α) × (Fin n → β))
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun h => (h.states, h.act1, h.act2)
      left_inv := by intro p; rfl
      right_inv := by intro h; rfl }

/-- The current state `i_{n+1}` of a history in `H_{n+1}`. -/
def History.last {n : ℕ} (h : History N α β n) : Fin N := h.states ⟨n, by omega⟩

/-- The initial segment of a history in `H_{n+1}` that lies in `H_{k+1}`, for `k < n`. -/
def History.prefix {n : ℕ} (h : History N α β n) (k : Fin n) : History N α β k.val where
  states := fun m => h.states ⟨m.val, by omega⟩
  act1 := fun m => h.act1 ⟨m.val, by omega⟩
  act2 := fun m => h.act2 ⟨m.val, by omega⟩

/-- A (randomized, history-dependent) policy `R_1 = (π^1, π^2, …)` for player I (p. 187):
`choose n h a` is `π^{n+1}` at the history `h ∈ H_{n+1}` and action `a`. It is nonnegative,
vanishes outside `A(i_{n+1})`, and sums to one. -/
structure Policy1 (G : Game N α β) where
  choose : ∀ n, History N α β n → α → ℝ
  choose_nonneg : ∀ n h a, 0 ≤ choose n h a
  choose_outside : ∀ n h a, a ∉ G.A h.last → choose n h a = 0
  choose_sum_one : ∀ n h, ∑ a : α, choose n h a = 1

/-- A (randomized, history-dependent) policy `R_2 = (ρ^1, ρ^2, …)` for player II (p. 187). -/
structure Policy2 (G : Game N α β) where
  choose : ∀ n, History N α β n → β → ℝ
  choose_nonneg : ∀ n h b, 0 ≤ choose n h b
  choose_outside : ∀ n h b, b ∉ G.B h.last → choose n h b = 0
  choose_sum_one : ∀ n h, ∑ b : β, choose n h b = 1

/-- A stationary decision rule `π` for player I: `π i a ≥ 0`, `π i a = 0` for `a ∉ A(i)`,
and `∑_a π i a = 1` for every state `i`. -/
def IsDecisionRule1 (G : Game N α β) (π : Fin N → α → ℝ) : Prop :=
  ∀ i, (∀ a, 0 ≤ π i a) ∧ (∀ a, a ∉ G.A i → π i a = 0) ∧ ∑ a : α, π i a = 1

/-- A stationary decision rule `ρ` for player II. -/
def IsDecisionRule2 (G : Game N α β) (ρ : Fin N → β → ℝ) : Prop :=
  ∀ i, (∀ b, 0 ≤ ρ i b) ∧ (∀ b, b ∉ G.B i → ρ i b = 0) ∧ ∑ b : β, ρ i b = 1

/-- The stationary policy `π^∞` of player I: the decision rule `π` used at every time point,
independently of the history except through the current state. -/
def stationary1 (G : Game N α β) (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) :
    Policy1 G where
  choose := fun _ h a => π h.last a
  choose_nonneg := fun _ h a => (hπ h.last).1 a
  choose_outside := fun _ h a ha => (hπ h.last).2.1 a ha
  choose_sum_one := fun _ h => (hπ h.last).2.2

/-- The stationary policy `ρ^∞` of player II. -/
def stationary2 (G : Game N α β) (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ) :
    Policy2 G where
  choose := fun _ h b => ρ h.last b
  choose_nonneg := fun _ h b => (hρ h.last).1 b
  choose_outside := fun _ h b hb => (hρ h.last).2.1 b hb
  choose_sum_one := fun _ h => (hρ h.last).2.2

/-- The probability of the history `h ∈ H_{n+1}` under `(R_1, R_2)`, given `X_1 = i`:
`P(X_1 = i_1, Y_1 = a_1, Z_1 = b_1, …, Z_n = b_n, X_{n+1} = i_{n+1} | X_1 = i)`. -/
def historyProb (G : Game N α β) (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ)
    (h : History N α β n) : ℝ :=
  (if h.states ⟨0, by omega⟩ = i then 1 else 0) *
    ∏ k : Fin n,
      R1.choose k.val (h.prefix k) (h.act1 k) * R2.choose k.val (h.prefix k) (h.act2 k) *
        G.p (h.states ⟨k.val, by omega⟩) (h.act1 k) (h.act2 k) (h.states ⟨k.val + 1, by omega⟩)

/-- `P_{R_1,R_2}(X_{n+1} = j, Y_{n+1} = a, Z_{n+1} = b | X_1 = i)` (p. 187), the probability that
at time `n + 1` the state is `j` and the players choose `a` and `b`. -/
def stateActionProb (G : Game N α β) (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ)
    (j : Fin N) (a : α) (b : β) : ℝ :=
  ∑ h : History N α β n,
    if h.last = j then historyProb G R1 R2 i n h * R1.choose n h a * R2.choose n h b else 0

/-- The expected reward `v_i^{n+1}(R_1, R_2)` in period `n + 1` from initial state `i` (p. 187). -/
def periodReward (G : Game N α β) (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) (n : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a : α, ∑ b : β, stateActionProb G R1 R2 i n j a b * G.r j a b

/-- The expected total reward `v_i(R_1, R_2) = ∑_{t=1}^∞ v_i^t(R_1, R_2)` (p. 188). Under
Assumption 6.2.1 the series converges absolutely for every pair of policies. -/
noncomputable def totalReward (G : Game N α β) (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N) :
    ℝ :=
  ∑' n : ℕ, periodReward G R1 R2 i n

/-- `(R_1^*, R_2^*)` is a pair of optimal policies for the TMG-model, (6.1.1) (p. 188):
`v(R_1, R_2^*) ≤ v(R_1^*, R_2^*) ≤ v(R_1^*, R_2)` componentwise, for all policies `R_1, R_2`. -/
def IsOptimalPair (G : Game N α β) (R1s : Policy1 G) (R2s : Policy2 G) : Prop :=
  ∀ (R1 : Policy1 G) (R2 : Policy2 G) (i : Fin N),
    totalReward G R1 R2s i ≤ totalReward G R1s R2s i ∧
      totalReward G R1s R2s i ≤ totalReward G R1s R2 i

/-- `y` is the value `val(TMG)` of the game: `y = v(R_1^*, R_2^*)` for a pair of optimal
policies `(R_1^*, R_2^*)` (p. 188). -/
def IsValueOfGame (G : Game N α β) (y : Fin N → ℝ) : Prop :=
  ∃ (R1 : Policy1 G) (R2 : Policy2 G), IsOptimalPair G R1 R2 ∧ ∀ i, y i = totalReward G R1 R2 i

end KallenbergLP.Games
