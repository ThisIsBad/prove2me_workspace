import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory

namespace KumarSeidman.Supervisor

variable {P M : ℕ}

/-- Condition (24) (p. 296) on the supervisor's run-length parameters `γ_m`:
`γ_m (1 − ρ_m) > Σ_{b ∈ B_m} max_{b' ∈ B_m} δ_{b',b}` for every machine `m`. -/
def GammaCondition (S : System P M) (γ : Fin M → ℝ) : Prop :=
  ∀ m, S.setupSum m < γ m * (1 - S.rho m)

/-- `ζ_m := γ_m (1 − ρ_m) − Σ_{b ∈ B_m} max_{b' ∈ B_m} δ_{b',b}`, equation (26) (p. 296). -/
noncomputable def zeta (S : System P M) (γ : Fin M → ℝ) (m : Fin M) : ℝ :=
  γ m * (1 - S.rho m) - S.setupSum m

/-- The truncation length `γ_m d_p τ_{p,i}` of a processing run of buffer `b = b_{p,i}`,
`m = μ_{p,i}`. -/
noncomputable def runCap (S : System P M) (γ : Fin M → ℝ) (b : Buffer S) : ℝ :=
  γ (S.mach b) * S.d b.1 * S.tau b

/-- The backlog `β_{p,i}(t) := Σ_{j=1}^{i} τ_{p,i} x_{p,j}(t)` of Lemma 1 2) (p. 296), for
`b = b_{p,i}`: every term carries the weight `τ_{p,i}` (as printed), the work machine `μ_{p,i}`
will spend on the parts now in the buffers `b_{p,1}, …, b_{p,i}`. -/
noncomputable def backlog {S : System P M} (T : Trajectory S) (b : Buffer S) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Iic b.2, S.tau b * T.x ⟨b.1, j⟩ t

namespace Trajectory

variable {S : System P M}

/-- Buffer `b` waits in the priority queue `Q_m` (`m = μ_b`) throughout some interval
`(t, t₁)`: on it, machine `m`'s current run is not on `b` and `x_b > z_b` (the two conditions
of the Rule for Entering `Q_m`; a waiting buffer leaves only when a set-up for it commences). -/
def WaitingAfter (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : Prop :=
  ∃ t₁ > t, ∀ σ ∈ Set.Ioo t t₁, ¬ T.OnRun b σ ∧ z b < T.x b σ

/-- The time at which the current sojourn of `b` in `Q_m` began, seen from the instant `t`:
the infimum of the `e ∈ [0, t]` such that `b` was waiting in `Q_m` at every time of `(e, t)`.
This is the FCFS key. All buffers waiting at time `0` share the key `0`, so the initial order
of `Q_m` is arbitrary. -/
noncomputable def entryTime (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : ℝ :=
  sInf {e : ℝ | e ∈ Set.Icc 0 t ∧ ∀ σ ∈ Set.Ioo e t, ¬ T.OnRun b σ ∧ z b < T.x b σ}

/-- The buffers in `Q_m` when run `k` of machine `m` terminates at `s_{k+1}`: every
`b ∈ B_m` with `x_b(s_{k+1}) > z_b`. This includes `β_k` itself if its level exceeds `z_{β_k}`
("after completing a processing run, a buffer may immediately enter `Q_m`", p. 296). -/
def queueAtSwitch (T : Trajectory S) (z : Buffer S → ℝ) (m : Fin M) (k : ℕ) : Set (Buffer S) :=
  {b | S.mach b = m ∧ z b < T.x b (T.s m (k + 1))}

/-- The trajectory obeys the supervisor of §V (p. 296) with parameters `γ` and `z`, on top of
an otherwise arbitrary scheduling policy:

* **Truncation Rule.** Every run terminates, and no processing run of `b_{p,i}` lasts longer
  than `γ_m d_p τ_{p,i}`.
* **Buffer Selection Rule** (with Entering/Leaving `Q_m`). If `Q_m ≠ ∅` when run `k`
  terminates, the next run is on a buffer of `Q_m` with the earliest entry time (FCFS; ties
  are broken arbitrarily).
* **Processing time for a buffer from `Q_m`.** Such a run processes its buffer for exactly
  `γ_m d_p τ_{p,i}` time units, unless the buffer clears earlier, in which case the run ends
  when it clears.

If `Q_m = ∅` when a run terminates, the next buffer is unrestricted. -/
structure Supervised (T : Trajectory S) (γ : Fin M → ℝ) (z : Buffer S → ℝ) : Prop where
  truncation : ∀ m (k : ℕ), (k : ℕ∞) < T.N m →
    T.HasNext m k ∧ T.s m (k + 1) - T.procStart m k ≤ runCap S γ (T.β m k)
  selection : ∀ m (k : ℕ), T.HasNext m k → (T.queueAtSwitch z m k).Nonempty →
    T.β m (k + 1) ∈ T.queueAtSwitch z m k ∧
      ∀ b ∈ T.queueAtSwitch z m k,
        T.entryTime z (T.β m (k + 1)) (T.s m (k + 1)) ≤ T.entryTime z b (T.s m (k + 1))
  queue_time : ∀ m (k : ℕ), T.HasNext m (k + 1) → (T.queueAtSwitch z m k).Nonempty →
    (∀ σ ∈ Set.Ico (T.procStart m (k + 1)) (T.s m (k + 2)), 0 < T.x (T.β m (k + 1)) σ) ∧
      (T.s m (k + 2) = T.procStart m (k + 1) + runCap S γ (T.β m (k + 1)) ∨
        T.x (T.β m (k + 1)) (T.s m (k + 2)) = 0)

/-- Buffer `b` is in `Q_m` at the instant `t`: it waits in `Q_m` just after `t`, or it is in
`Q_m` at a run termination `t = s_{k+1}` and is taken up for processing at that instant. -/
def QueuedAt (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : Prop :=
  0 ≤ t ∧ (T.WaitingAfter z b t ∨
    ∃ k : ℕ, T.HasNext (S.mach b) k ∧ T.s (S.mach b) (k + 1) = t ∧
      T.β (S.mach b) (k + 1) = b ∧ z b < T.x b t)

/-- Buffer `b` enters `Q_m` at the instant `t`: it is in `Q_m` at `t`, and `t = 0` or it was
not waiting in `Q_m` at any time of some interval `(t₀, t)`. -/
def EntersQ (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (t : ℝ) : Prop :=
  T.QueuedAt z b t ∧ (t = 0 ∨ ∃ t₀ < t, ∀ σ ∈ Set.Ioo t₀ t, ¬ T.WaitingAfter z b σ)

/-- Run `k` of machine `μ_b` is the first processing run of `b` subsequent to the instant `t`:
it is on `b`, starts at or after `t` and ends after `t`, and no earlier run on `b` does both.
Its completion time is `s_{k+1}`. -/
def IsNextRun (T : Trajectory S) (b : Buffer S) (t : ℝ) (k : ℕ) : Prop :=
  (k : ℕ∞) < T.N (S.mach b) ∧ T.β (S.mach b) k = b ∧ t ≤ T.s (S.mach b) k ∧
    (T.HasNext (S.mach b) k → t < T.s (S.mach b) (k + 1)) ∧
    ∀ j < k, T.β (S.mach b) j = b →
      ¬ (t ≤ T.s (S.mach b) j ∧ (T.HasNext (S.mach b) j → t < T.s (S.mach b) (j + 1)))

end Trajectory

end KumarSeidman.Supervisor
