import Mathlib

namespace BakerScudder1990.Tolerance

/-- A single-machine earliness/tardiness instance with a common due date and due-date
tolerances, for a **fixed job sequence** (Baker and Scudder, Oper. Res. 38 (1990), p. 23 and
pp. 29–30). Jobs are indexed by their 0-based position `j : Fin n` in the sequence (the paper's
job `j + 1`). Job `j` has processing time `p j`, tolerances `u j` (before the due date) and
`v j` (after it), unit earliness penalty `α j > 0` and unit tardiness penalty `β j > 0`
(p. 23); the tolerances are nonnegative, so the penalty-free window `[d - u j, d + v j]` is an
interval (p. 29). The tolerance condition `p_j - v_j - u_i > 0` (p. 30, "at most one job can
avoid penalty costs") is imposed for distinct jobs `i ≠ j`. -/
structure Instance (n : ℕ) where
  /-- processing times `p_j` -/
  p : Fin n → ℝ
  /-- tolerance before the due date, `u_j` -/
  u : Fin n → ℝ
  /-- tolerance after the due date, `v_j` -/
  v : Fin n → ℝ
  /-- unit earliness penalties `α_j` -/
  α : Fin n → ℝ
  /-- unit tardiness penalties `β_j` -/
  β : Fin n → ℝ
  hα : ∀ j, 0 < α j
  hβ : ∀ j, 0 < β j
  hu : ∀ j, 0 ≤ u j
  hv : ∀ j, 0 ≤ v j
  /-- tolerance condition `p_j - v_j - u_i > 0` for distinct jobs `i ≠ j` (p. 30) -/
  htol : ∀ i j, i ≠ j → u i + v j < p j

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Completion time of the job in position `j` when the sequence is processed from time `0`
without inserted idle time: `C_j = ∑_{i ≤ j} p_i`. -/
def C (j : Fin n) : ℝ := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ j), I.p i

/-- Earliness of job `j` measured from the end of its tolerance window, for due date `d`:
`E_j = (d - C_j - u_j)^+` (p. 30). -/
def earliness (d : ℝ) (j : Fin n) : ℝ := max 0 (d - I.C j - I.u j)

/-- Tardiness of job `j` measured from the end of its tolerance window, for due date `d`:
`T_j = (C_j - d - v_j)^+` (p. 30). -/
def tardiness (d : ℝ) (j : Fin n) : ℝ := max 0 (I.C j - d - I.v j)

/-- Total penalty `f = ∑_j (α_j E_j + β_j T_j)` as a function of the common due date `d`
(p. 30). -/
def cost (d : ℝ) : ℝ := ∑ j, (I.α j * I.earliness d j + I.β j * I.tardiness d j)

/-- `d` is an optimal due date for the fixed sequence: it minimizes the total penalty over all
real due dates. -/
def IsOptimalDueDate (d : ℝ) : Prop := ∀ d' : ℝ, I.cost d ≤ I.cost d'

/-- `d` is the least optimal due date: optimal, and no smaller due date is optimal (the paper's
secondary criterion "minimize d … when there are alternative optima", p. 34). -/
def IsLeastOptimalDueDate (d : ℝ) : Prop :=
  I.IsOptimalDueDate d ∧ ∀ d' : ℝ, I.IsOptimalDueDate d' → d ≤ d'

end Instance

end BakerScudder1990.Tolerance
