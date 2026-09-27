import Mathlib

namespace ComplexScheduling

variable {n r : ℕ}

/-- Activity `i` is in process at the integer time `t` under the schedule `S`: it has started
and has not yet completed.  Brucker and Knust, *Complex Scheduling*, §1.1, p. 1. -/
def InProcess (p : Fin n → ℕ) (S : Fin n → ℕ) (t : ℕ) (i : Fin n) : Prop :=
  S i ≤ t ∧ t < S i + p i

instance (p : Fin n → ℕ) (S : Fin n → ℕ) (t : ℕ) : DecidablePred (InProcess p S t) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The total amount of resource `k` occupied at time `t`: activity `i` occupies `demand i k`
units throughout its processing.  Brucker and Knust §1.1, p. 1. -/
def resourceUsage (p : Fin n → ℕ) (demand : Fin n → Fin r → ℕ) (S : Fin n → ℕ)
    (k : Fin r) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (InProcess p S t), demand i k

/-- A schedule assigns each activity an integer starting time; it is **feasible** when the
precedence constraints `i → j`, given as pairs in `prec`, are met — `S i + p i ≤ S j` — and when
at every time the demand for each resource is within its capacity.  Brucker and Knust §1.1,
pp. 1-2. -/
def FeasibleSchedule (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  (∀ e ∈ prec, S e.1 + p e.1 ≤ S e.2) ∧
    ∀ (k : Fin r) (t : ℕ), resourceUsage p demand S k t ≤ Rcap k

/-- The schedule obtained from `S` by starting activity `i` at time `s` instead, every other
activity left where it was. -/
def restart (S : Fin n → ℕ) (i : Fin n) (s : ℕ) : Fin n → ℕ := Function.update S i s

/-- A **left shift** of activity `i` to time `s`: `s < S i` and the result is feasible, all other
activities unmoved.  Brucker and Knust §3.1.2, p. 119. -/
def LeftShiftTo (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) (i : Fin n) (s : ℕ) : Prop :=
  s < S i ∧ FeasibleSchedule p Rcap demand prec (restart S i s)

/-- A **local left shift**: a left shift reachable by successive one-period left shifts, so every
intermediate schedule — the start of `i` lowered one time unit at a time — is itself feasible.
Brucker and Knust §3.1.2, pp. 119-120. -/
def LocalLeftShiftTo (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) (i : Fin n) (s : ℕ) : Prop :=
  s < S i ∧ ∀ u : ℕ, s ≤ u → u ≤ S i → FeasibleSchedule p Rcap demand prec (restart S i u)

/-- A feasible schedule is **semi-active** when no local left shift is possible for any activity.
Brucker and Knust §3.1.2, p. 120. -/
def SemiActive (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  FeasibleSchedule p Rcap demand prec S ∧
    ∀ (i : Fin n) (s : ℕ), ¬ LocalLeftShiftTo p Rcap demand prec S i s

/-- A feasible schedule is **active** when no left shift at all — local or global — is possible
for any activity.  Brucker and Knust §3.1.2, p. 120. -/
def Active (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  FeasibleSchedule p Rcap demand prec S ∧
    ∀ (i : Fin n) (s : ℕ), ¬ LeftShiftTo p Rcap demand prec S i s

/-- The completion times `C i = S i + p i` of a schedule.  Brucker and Knust §1.1, p. 2. -/
def completion (p : Fin n → ℕ) (S : Fin n → ℕ) : Fin n → ℕ := fun i => S i + p i

/-- An objective is **regular** when it is monotone nondecreasing in the completion times:
`f C ≤ f C'` whenever `C i ≤ C' i` for every activity.  Brucker and Knust §1.2, p. 18. -/
def Regular (f : (Fin n → ℕ) → ℝ) : Prop :=
  ∀ C C' : Fin n → ℕ, (∀ i, C i ≤ C' i) → f C ≤ f C'

/-- The objective value of a schedule: `f` evaluated at its completion-time vector. -/
def scheduleValue (p : Fin n → ℕ) (f : (Fin n → ℕ) → ℝ) (S : Fin n → ℕ) : ℝ :=
  f (completion p S)

/-- `S` is optimal when no feasible schedule has a smaller objective value. -/
def IsOptimalSchedule (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (f : (Fin n → ℕ) → ℝ) (S : Fin n → ℕ) : Prop :=
  FeasibleSchedule p Rcap demand prec S ∧
    ∀ S' : Fin n → ℕ, FeasibleSchedule p Rcap demand prec S' →
      scheduleValue p f S ≤ scheduleValue p f S'

end ComplexScheduling
