import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_IgnallSchrage_Invariance_Node
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Invariance

/-- The machine completion triple after one more job: from `(TA, TB, TC)` and job `i`,
machine A finishes at `TA + a i`, machine B at `max TB (TA + a i) + b i`, machine C at
`max TC (that B time) + c i`. This is exactly the step of
`JohnsonFlowShop.ThreeStage.asapDone`. -/
def appendJob3 {n : ℕ} (a b c : Fin n → ℝ) (t : ℝ × ℝ × ℝ) (i : Fin n) : ℝ × ℝ × ℝ :=
  let d₁ := t.1 + a i
  let d₂ := max t.2.1 d₁ + b i
  (d₁, d₂, max t.2.2 d₂ + c i)

/-- `times3 a b c J = (TIMEA(J), TIMEB(J), TIMEC(J))` for a node `J` (a partial sequence, the
list of the jobs scheduled so far, in order): the times at which machines A, B and C finish the
last of the jobs of `J` when they are processed in the order of `J`, as early as possible,
starting from time `0` (p. 401). For `J = []` it is `(0, 0, 0)`. Whenever `J` is the list of the
first `r` positions of an order `σ`, `times3 a b c J` coincides with Johnson's
`JohnsonFlowShop.ThreeStage.asapDone a b c σ r`, since both apply `appendJob3` position by
position. -/
def times3 {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ × ℝ × ℝ :=
  J.foldl (appendJob3 a b c) (0, 0, 0)

/-- The three-machine lower bound of Ignall and Schrage (p. 401) of a node `J = J_r`, with
`J̄_r` its set of unscheduled jobs:
`LB(J_r) = max [ TIMEA(J_r) + Σ_{J̄_r} a_i + min_{J̄_r} (b_i + c_i),
                 TIMEB(J_r) + Σ_{J̄_r} b_i + min_{J̄_r} c_i,
                 TIMEC(J_r) + Σ_{J̄_r} c_i ]`.
It is meant for nodes with `J̄_r` nonempty (`r ≤ n - 1`), where the minima are genuine minima;
the procedure never evaluates it at a node with `J̄_r = ∅`. -/
def lowerBound3 {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  let t := times3 a b c J
  let U := IgnallSchrage.Makespan.unscheduled J
  max (t.1 + ∑ i ∈ U, a i + IgnallSchrage.Makespan.minOver U (fun i => b i + c i))
    (max (t.2.1 + ∑ i ∈ U, b i + IgnallSchrage.Makespan.minOver U c)
      (t.2.2 + ∑ i ∈ U, c i))

end IgnallSchrage.Invariance
