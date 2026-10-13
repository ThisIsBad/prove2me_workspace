import Mathlib

open scoped ENNReal NNReal

namespace SennottDP.Discounted

/-- Sennott (1999), §2.1, p. 16: a Markov decision chain `Δ`. The state space `S` is countable;
each state `i` has a finite nonempty set `A i` of actions; choosing `a ∈ A i` in state `i` incurs
a nonnegative finite cost `C i a`, and the next state is `j` with probability `P i a j`, where
`∑ j, P i a j = 1` for every admissible action `a ∈ A i`. -/
structure MDC (S : Type) [Countable S] (Act : Type) where
  /-- the finite action set `A_i` available in state `i` -/
  A : S → Finset Act
  /-- every action set is nonempty -/
  A_nonempty : ∀ i, (A i).Nonempty
  /-- the nonnegative finite cost `C(i,a)` -/
  C : S → Act → ℝ≥0
  /-- the transition probability `P_{ij}(a)` -/
  P : S → Act → S → ℝ≥0∞
  /-- `∑_j P_{ij}(a) = 1` for `a ∈ A_i` -/
  P_sum : ∀ i, ∀ a ∈ A i, ∑' j, P i a j = 1

/-- Sennott (1999), §2.2, pp. 20–22: a general (history-dependent, randomized) policy `θ` for the
infinite horizon. A history at time `n` is `h_n = (i_0, a_0, i_1, …, a_{n-1}, i_n)`, encoded as the
state sequence `s : Fin (n+1) → S` (with `s k = i_k`) and the action sequence `as : Fin n → Act`
(with `as k = a_k`). `dist n s as` is the probability distribution `θ(· | h_n)` of the action at
time `n`: it is supported on the action set `A_{i_n}` of the current state and sums to one. -/
structure Policy {S : Type} [Countable S] {Act : Type} (M : MDC S Act) where
  /-- `dist n s as a = θ(a | h_n)` -/
  dist : (n : ℕ) → (Fin (n + 1) → S) → (Fin n → Act) → Act → ℝ≥0∞
  /-- `θ(· | h_n)` puts no mass outside `A_{i_n}` -/
  dist_supp : ∀ n s as a, a ∉ M.A (s (Fin.last n)) → dist n s as a = 0
  /-- `θ(· | h_n)` is a probability distribution on `A_{i_n}` -/
  dist_sum : ∀ n s as, ∑ a ∈ M.A (s (Fin.last n)), dist n s as a = 1

/-- Sennott (1999), §2.2, p. 20: a stationary policy `f` chooses the action `f(i) ∈ A_i` whenever
the current state is `i`. -/
def StationaryPolicy {S : Type} [Countable S] {Act : Type} (M : MDC S Act) : Type :=
  {f : S → Act // ∀ i, f i ∈ M.A i}

open Classical in
/-- A stationary policy `f` viewed as a general policy: at every time `n` and after every history
`h_n`, it chooses the action `f(i_n)` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type} {M : MDC S Act}
    (f : StationaryPolicy M) : Policy M where
  dist n s _ a := if a = f.1 (s (Fin.last n)) then 1 else 0
  dist_supp n s _ a ha := by
    have hne : a ≠ f.1 (s (Fin.last n)) := fun h => ha (h ▸ f.2 _)
    simp [hne]
  dist_sum n s _ := by
    simp [f.2 (s (Fin.last n))]

end SennottDP.Discounted
