import Mathlib

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- A Markov decision chain (Sennott, §2.1, p. 16): a countable state space `S`, for each state
`i` a finite nonempty set of actions `A i`, nonnegative finite costs `C i a`, and transition
probabilities `P i a j` with `∑' j, P i a j = 1`. -/
structure MDC (S : Type*) (Act : Type*) [Countable S] where
  /-- the finite action set available in state `i` -/
  A : S → Finset Act
  /-- every action set is nonempty -/
  A_nonempty : ∀ i, (A i).Nonempty
  /-- the (finite, nonnegative) one-step cost -/
  C : S → Act → ℝ≥0
  /-- the transition probability from `i` to `j` under action `a` -/
  P : S → Act → S → ℝ≥0∞
  /-- each row is a probability distribution on `S` -/
  P_sum : ∀ i a, ∑' j, P i a j = 1

variable {S : Type*} {Act : Type*} [Countable S]

/-- A general (history-dependent, randomized) policy for the infinite horizon (§2.2, p. 20).
At time `n` with history `h_n = (i_0, a_0, …, i_{n-1}, a_{n-1}, i_n)` the action is drawn from the
distribution `θ(· | h_n)` on `A_{i_n}`. The history is encoded by the list of past state-action
pairs, **most recent first**, together with the current state: `prob [(i_{n-1},a_{n-1}), …,
(i_0,a_0)] i_n a = θ(a | h_n)`. -/
structure Policy (M : MDC S Act) where
  /-- `prob past i a` is the probability of choosing `a` in current state `i` after `past` -/
  prob : List (S × Act) → S → Act → ℝ≥0∞
  /-- only actions of `A i` are chosen -/
  prob_supp : ∀ past i a, a ∉ M.A i → prob past i a = 0
  /-- the choice is a probability distribution on `A i` -/
  prob_sum : ∀ past i, ∑ a ∈ M.A i, prob past i a = 1

/-- A (deterministic) stationary policy `f` (§2.2, p. 20): a distinguished action `f i ∈ A i` for
every state. -/
structure StationaryPolicy (M : MDC S Act) where
  /-- the action chosen in state `i` -/
  f : S → Act
  /-- the action is admissible -/
  mem : ∀ i, f i ∈ M.A i

open Classical in
/-- A stationary policy regarded as a general policy: it chooses `f i` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {M : MDC S Act} (e : StationaryPolicy M) :
    Policy M where
  prob := fun _ i a => if a = e.f i then 1 else 0
  prob_supp := by
    intro past i a ha
    have : a ≠ e.f i := fun h => ha (h ▸ e.mem i)
    simp [this]
  prob_sum := by
    intro past i
    simp [e.mem i]

open Classical in
/-- Weight of the transition into the state `j` that follows the (most-recent-first) list `rest`:
the initial indicator `1{j = i}` if `rest` is empty, and `P_{k j}(b)` if the last pair of `rest`
is `(k, b)`. -/
noncomputable def prevWeight (M : MDC S Act) (i : S) : List (S × Act) → S → ℝ≥0∞
  | [], j => if j = i then 1 else 0
  | (k, b) :: _, j => M.P k b j

/-- `histProb θ i h` is `P_θ(X_0 = i_0, A_0 = a_0, …, X_t = i_t, A_t = a_t | X_0 = i)` for the list
`h = [(i_t,a_t), …, (i_0,a_0)]` (most recent first) (§2.3, pp. 22–23). -/
noncomputable def histProb {M : MDC S Act} (θ : Policy M) (i : S) : List (S × Act) → ℝ≥0∞
  | [] => 1
  | (j, a) :: rest => histProb θ i rest * prevWeight M i rest j * θ.prob rest j a

/-- The cost of the most recent state-action pair of a history (`0` for the empty list). -/
noncomputable def lastCost (M : MDC S Act) : List (S × Act) → ℝ≥0∞
  | [] => 0
  | (j, a) :: _ => (M.C j a : ℝ≥0∞)

/-- The statistical average cost at time `t`, `E_θ[C(X_t, A_t) | X_0 = i]` (2.6), p. 23: the sum
of `C(i_t, a_t)` against the law of the length-`(t+1)` state-action history. Valued in `[0, ∞]`. -/
noncomputable def expCost {M : MDC S Act} (θ : Policy M) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : List (S × Act), if h.length = t + 1 then histProb θ i h * lastCost M h else 0

end SennottDP.AvgFinite
