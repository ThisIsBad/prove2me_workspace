import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule

namespace IgnallSchrage.Makespan

/-- The machine completion triple after one more job: from `(TA, TB, TC)` and job `i`,
machine A finishes at `TA + a i`, machine B at `max TB (TA + a i) + b i`, machine C at
`max TC (that B time) + c i`. This is exactly the step of
`JohnsonFlowShop.ThreeStage.asapDone`. -/
def appendJob {n : ℕ} (a b c : Fin n → ℝ) (t : ℝ × ℝ × ℝ) (i : Fin n) : ℝ × ℝ × ℝ :=
  let d₁ := t.1 + a i
  let d₂ := max t.2.1 d₁ + b i
  (d₁, d₂, max t.2.2 d₂ + c i)

/-- `times a b c J = (TIMEA(J), TIMEB(J), TIMEC(J))` for a node `J` (a partial sequence, the
list of the jobs scheduled so far, in order): the times at which machines A, B and C finish the
last of the jobs of `J` when they are processed in the order of `J`, as early as possible,
starting from time `0`. For `J = []` it is `(0, 0, 0)`. Whenever `J` is the list of the first
`r` positions of an order `σ` (`J = (List.ofFn σ).take r`), `times a b c J` coincides with
Johnson's `JohnsonFlowShop.ThreeStage.asapDone a b c σ r`, since both apply `appendJob`
position by position. -/
def times {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ × ℝ × ℝ :=
  J.foldl (appendJob a b c) (0, 0, 0)

/-- `unscheduled J` is the set `J̄` of jobs that have not been assigned a position in the
partial sequence `J`. -/
def unscheduled {n : ℕ} (J : List (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ∉ J)

/-- The makespan of a full sequence `σ` (`σ k` = job in position `k`): the time machine C
finishes the last job, `TIMEC` after all `n` positions of Johnson's as-soon-as-possible
schedule. -/
def makespan {n : ℕ} (a b c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (JohnsonFlowShop.ThreeStage.asapDone a b c σ n).2.2

/-- The full sequence `σ` begins with the partial sequence `J`: `J` is a prefix of the list
`[σ 0, σ 1, …, σ (n-1)]`, i.e. `σ k = J[k]` for every position `k < J.length`. -/
def BeginsWith {n : ℕ} (σ : Equiv.Perm (Fin n)) (J : List (Fin n)) : Prop :=
  J <+: List.ofFn σ

end IgnallSchrage.Makespan
