import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Makespan

/-- The minimum of `f` over a finite set of jobs `s`, `min_{i ∈ s} f i`, when `s` is nonempty
(`Finset.inf'`). The value `0` on the empty set is a placeholder: every statement of the
mission evaluates it only on a nonempty `s`. -/
def minOver {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

/-- The lower bound of Ignall and Schrage (p. 401) of a node `J = J_r` with `J̄_r` its set of
unscheduled jobs:
`LB(J_r) = max [ TIMEA(J_r) + Σ_{J̄_r} a_i + min_{J̄_r} (b_i + c_i),
                 TIMEB(J_r) + Σ_{J̄_r} b_i + min_{J̄_r} c_i,
                 TIMEC(J_r) + Σ_{J̄_r} c_i ]`.
It is meant for nodes with `J̄_r` nonempty (`r ≤ n - 1`), where the minima are genuine
minima; the procedure never evaluates it at a node with `J̄_r = ∅`. -/
def lowerBound {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  let t := times a b c J
  let U := unscheduled J
  max (t.1 + (∑ i ∈ U, a i) + minOver U (fun i => b i + c i))
    (max (t.2.1 + (∑ i ∈ U, b i) + minOver U c)
      (t.2.2 + ∑ i ∈ U, c i))

end IgnallSchrage.Makespan
