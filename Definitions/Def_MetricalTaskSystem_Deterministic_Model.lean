import Mathlib

namespace MetricalTaskSystem.Deterministic

/-- A **task system** `(S, d)` (Borodin–Linial–Saks 1992, p. 746): the transition-cost matrix
`d` has zero diagonal, positive off-diagonal entries and satisfies the triangle inequality
`d(i, j) + d(j, k) ≥ d(i, k)`. The state set `S` is a finite type (the paper's `{1, …, n}`). -/
structure IsTaskSystem {S : Type} (d : S → S → ℝ) : Prop where
  diag : ∀ i, d i i = 0
  pos : ∀ i j, i ≠ j → 0 < d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k

/-- A task system is **metrical** if, in addition, `d` is symmetric (p. 747). -/
def IsMetrical {S : Type} (d : S → S → ℝ) : Prop :=
  IsTaskSystem d ∧ ∀ i j, d i j = d j i

/-- The cost `c(T; σ)` of a schedule (p. 747) for a task sequence of length `m`.
Task `T i` (for `i : Fin m`) is the paper's `T^{i+1}`; a schedule is `σ : Fin (m+1) → S`,
where `σ 0` is the initial state and `σ (i+1)` is the state in which `T^{i+1}` is processed:
`c(T; σ) = Σ_{i=1}^m d(σ(i−1), σ(i)) + Σ_{i=1}^m T^i(σ(i))`. -/
def schedCost {S : Type} (d : S → S → ℝ) {m : ℕ} (T : Fin m → S → ℝ)
    (σ : Fin (m + 1) → S) : ℝ :=
  ∑ i : Fin m, (d (σ i.castSucc) (σ i.succ) + T i (σ i.succ))

/-- The optimal off-line cost `c₀(T)` (p. 747): the minimum of `c(T; σ)` over the finitely many
schedules `σ` with `σ 0 = s₀`. -/
noncomputable def offlineOpt {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ) (s₀ : S)
    {m : ℕ} (T : Fin m → S → ℝ) : ℝ :=
  (Finset.univ.filter (fun σ : Fin (m + 1) → S => σ 0 = s₀)).inf'
    ⟨fun _ => s₀, by simp⟩ (fun σ => schedCost d T σ)

/-- An **on-line (deterministic, discrete-time) scheduling algorithm** (p. 747): the state
`σ(i)` is a function of the initial state `s₀` and of the first `i` tasks `T¹ ⋯ Tⁱ` only.
It is encoded as the map `(s₀, [T¹, …, Tⁱ]) ↦ σ(i)`; its value on the empty list is never
used, since `σ(0) = s₀`. -/
abbrev OnlineAlgorithm (S : Type) : Type := S → List (S → ℝ) → S

/-- The schedule `σ = A(T)` that the on-line algorithm `A` produces on `T¹ ⋯ Tᵐ` from `s₀`:
`σ(0) = s₀` and `σ(i) = A(s₀, [T¹, …, Tⁱ])` for `1 ≤ i ≤ m`. -/
def onlineSchedule {S : Type} (A : OnlineAlgorithm S) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) :
    Fin (m + 1) → S :=
  fun i => if (i : ℕ) = 0 then s₀ else A s₀ ((List.ofFn T).take i)

/-- The cost `c_A(T) = c(T; A(T))` of an on-line algorithm (p. 747). -/
def onlineCost {S : Type} (d : S → S → ℝ) (A : OnlineAlgorithm S) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) : ℝ :=
  schedCost d T (onlineSchedule A s₀ T)

/-- `A` is **`w`-competitive** (p. 747): `w > 0` and there is a constant `K` such that
`c_A(T) − w·c₀(T) ≤ K` for every finite task sequence `T` (with any initial state `s₀`).
Tasks are finite and nonnegative. The inequality is written additively. -/
def IsCompetitive {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ)
    (A : OnlineAlgorithm S) (w : ℝ) : Prop :=
  0 < w ∧ ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
    onlineCost d A s₀ T ≤ w * offlineOpt d s₀ T + K

/-- The **competitive ratio of the task system** `w(S, d)` (p. 747): the infimum over on-line
algorithms `A` of `w(A) = inf W_A`, where `W_A = {w : A is w-competitive}`. It is written as
the infimum of the union `⋃_A W_A`, which has the same value as `inf_A inf W_A` when
`inf ∅ = +∞`. (If no algorithm were competitive, the real `sInf ∅` would be `0`.) -/
noncomputable def competitiveRatio {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ A : OnlineAlgorithm S, IsCompetitive d A w}

end MetricalTaskSystem.Deterministic
