import Mathlib

namespace MarkovDecisionProcesses

/-- A **stationary** infinite-horizon Markov decision process on finite state and action spaces:
rewards `r(s, a)` and transition probabilities `p(j | s, a)` that do not depend on the decision
epoch (Assumption 8.0.1), with finitely many states (Assumption 8.0.3) and finitely many
admissible actions in each state.  Rewards are then automatically bounded (Assumption 8.0.2).
Puterman, *Markov Decision Processes*, §2.1, pp. 17-20, and §8.0, p. 331. -/
structure StationaryMDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- `A_s`, the admissible actions in state `s`. -/
  admissible : S → Finset A
  admissible_nonempty : ∀ s, (admissible s).Nonempty
  /-- `r(s, a)`, the stationary reward. -/
  reward : S → A → ℝ
  /-- `p(j | s, a)`, the stationary transition probability. -/
  trans : S → A → S → ℝ
  trans_nonneg : ∀ s a j, 0 ≤ trans s a j
  trans_sum : ∀ s a, ∑ j, trans s a j = 1

variable {S A : Type*} [Fintype S] [Fintype A]

/-- A **history-dependent randomized policy** `π ∈ Π^HR`: at decision epoch `t`, after the
history `h` of past state-action pairs, in state `s`, it chooses action `a` with probability
`q t h s a`, supported on the admissible actions.  Puterman §2.1, pp. 21-22. -/
structure AvgHRPolicy (M : StationaryMDP S A) where
  q : ℕ → List (S × A) → S → A → ℝ
  nonneg : ∀ t h s a, 0 ≤ q t h s a
  sum_one : ∀ t h s, ∑ a ∈ M.admissible s, q t h s a = 1

/-- The **deterministic stationary policy** `d^∞` that uses the decision rule `d : S → A` at
every epoch, whatever the history.  Puterman §2.1, p. 22, and §8.0. -/
noncomputable def stationaryPolicy (M : StationaryMDP S A) [DecidableEq A] (d : S → A)
    (hd : ∀ s, d s ∈ M.admissible s) : AvgHRPolicy M where
  q := fun _ _ s a => if a = d s then 1 else 0
  nonneg := by intro t h s a; by_cases hA : a = d s <;> simp [hA]
  sum_one := by
    intro t h s
    rw [Finset.sum_ite_eq' (M.admissible s) (d s) (fun _ => (1 : ℝ))]
    simp [hd s]

/-- The expected **total reward over `N` decision epochs**, `v^π_{N+1}(s) = E^π_s[∑_{t=1}^N r(X_t, Y_t)]`
of (8.1.2), for the policy `π` started at epoch `t` after history `h` in state `s`, computed by
the policy-evaluation recursion (Theorem 4.2.1 with zero terminal reward).  The first argument
is the number of decision epochs `N`.  Puterman §8.1.1, p. 332. -/
noncomputable def totalReward {M : StationaryMDP S A} (π : AvgHRPolicy M) :
    ℕ → ℕ → List (S × A) → S → ℝ
  | 0, _, _, _ => 0
  | (k + 1), t, h, s =>
      ∑ a ∈ M.admissible s, π.q t h s a *
        (M.reward s a + ∑ j, M.trans s a j * totalReward π k (t + 1) (h ++ [(s, a)]) j)

/-- The **lim sup average reward** `g^π_+(s) = lim sup_{N→∞} N⁻¹ v^π_{N+1}(s)` of (8.1.5).
Puterman §8.1.1, p. 334. -/
noncomputable def gainSup {M : StationaryMDP S A} (π : AvgHRPolicy M) (s : S) : ℝ :=
  Filter.limsup (fun N : ℕ => totalReward π N 0 [] s / N) Filter.atTop

/-- The **lim inf average reward** `g^π_-(s) = lim inf_{N→∞} N⁻¹ v^π_{N+1}(s)` of (8.1.6).
Puterman §8.1.1, p. 334. -/
noncomputable def gainInf {M : StationaryMDP S A} (π : AvgHRPolicy M) (s : S) : ℝ :=
  Filter.liminf (fun N : ℕ => totalReward π N 0 [] s / N) Filter.atTop

/-- `g^*_+(s) = sup_{π ∈ Π^HR} g^π_+(s)`, (8.1.10).  Puterman §8.1.2, p. 334. -/
noncomputable def optGainSup (M : StationaryMDP S A) (s : S) : ℝ :=
  ⨆ π : AvgHRPolicy M, gainSup π s

/-- `g^*_-(s) = sup_{π ∈ Π^HR} g^π_-(s)`, (8.1.11).  Puterman §8.1.2, p. 334. -/
noncomputable def optGainInf (M : StationaryMDP S A) (s : S) : ℝ :=
  ⨆ π : AvgHRPolicy M, gainInf π s

/-- A policy `π*` is **average optimal**, (8.1.7): `g^{π*}_-(s) ≥ g^π_+(s)` for all states `s` and
all `π ∈ Π^HR`, the strongest of the three criteria of §8.1.2.  Puterman p. 334. -/
def IsAverageOptimal {M : StationaryMDP S A} (πstar : AvgHRPolicy M) : Prop :=
  ∀ (π : AvgHRPolicy M) (s : S), gainSup π s ≤ gainInf πstar s

/-- The **unichain optimality residual** `B(g, h)(s) = max_{a ∈ A_s} { r(s,a) − g + ∑_j p(j|s,a) h(j) − h(s) }`
of (8.4.2)-(8.4.3); the average reward optimality equation is `B(g, h) = 0`.  Puterman §8.4.1,
p. 354. -/
noncomputable def optimalityResidual (M : StationaryMDP S A) (g : ℝ) (h : S → ℝ) (s : S) : ℝ :=
  (M.admissible s).sup' (M.admissible_nonempty s)
    (fun a => M.reward s a - g + ∑ j, M.trans s a j * h j - h s)

/-- A decision rule `d` is **`h`-improving**, (8.4.15): at every state it attains
`max_{a ∈ A_s} { r(s,a) + ∑_j p(j|s,a) h(j) }`.  Puterman §8.4.3, pp. 360-361. -/
def IsImproving (M : StationaryMDP S A) (h : S → ℝ) (d : S → A) : Prop :=
  ∀ s, d s ∈ M.admissible s ∧
    M.reward s (d s) + ∑ j, M.trans s (d s) j * h j
      = (M.admissible s).sup' (M.admissible_nonempty s)
          (fun a => M.reward s a + ∑ j, M.trans s a j * h j)

/-- The transition matrix `P_d` of the stationary policy `d^∞`. -/
def transMatrix (M : StationaryMDP S A) (d : S → A) : S → S → ℝ := fun i j => M.trans i (d i) j

/-- State `j` is **accessible** from state `i` under the transition matrix `P`: there is a path
of transitions of positive probability from `i` to `j` (of length zero allowed). -/
def Accessible (P : S → S → ℝ) : S → S → Prop :=
  Relation.ReflTransGen (fun i j => 0 < P i j)

/-- A state is **recurrent** for a finite-state transition matrix when every state accessible
from it leads back to it, i.e. it lies in a closed communicating class.  Puterman, Appendix A. -/
def IsRecurrent (P : S → S → ℝ) (i : S) : Prop :=
  ∀ j, Accessible P i j → Accessible P j i

/-- A finite-state transition matrix is **unichain** when it consists of a single recurrent
class plus a possibly empty set of transient states: any two recurrent states communicate.
Puterman §8.3.1, p. 348, and Appendix A. -/
def IsUnichainMatrix (P : S → S → ℝ) : Prop :=
  ∀ i j, IsRecurrent P i → IsRecurrent P j → Accessible P i j

/-- A **unichain** MDP: the transition matrix of every deterministic stationary policy is
unichain.  Puterman §8.3.1, p. 348 (b). -/
def IsUnichain (M : StationaryMDP S A) : Prop :=
  ∀ d : S → A, (∀ s, d s ∈ M.admissible s) → IsUnichainMatrix (transMatrix M d)

end MarkovDecisionProcesses
