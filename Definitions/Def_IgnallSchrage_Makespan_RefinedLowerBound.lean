import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- The refined lower bound of p. 409: the bound `lowerBound` of p. 401 with
`TIMEB(J_r)` replaced by `max [TIMEB(J_r), TIMEA(J_r) + min_{J̄_r} a_i]` and
`TIMEC(J_r)` replaced by
`max [TIMEC(J_r), TIMEB(J_r) + min_{J̄_r} b_i, TIMEA(J_r) + min_{J̄_r} (a_i + b_i)]`
(the original, unreplaced `TIMEA`, `TIMEB` inside the replacements). Meant for nodes with
`J̄_r` nonempty. -/
def refinedLowerBound {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  let t := times a b c J
  let U := unscheduled J
  let tB := max t.2.1 (t.1 + minOver U a)
  let tC := max t.2.2 (max (t.2.1 + minOver U b) (t.1 + minOver U (fun i => a i + b i)))
  max (t.1 + ∑ i ∈ U, a i + minOver U (fun i => b i + c i))
    (max (tB + ∑ i ∈ U, b i + minOver U c)
      (tC + ∑ i ∈ U, c i))

end IgnallSchrage.Makespan
