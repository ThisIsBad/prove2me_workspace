import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork

namespace CriticalPath.CostCurve

variable {n : ℕ}

/-- The predecessors of event `j`: the events `i` with `i < j` and `(i, j) ∈ P`. -/
def preds (N : ProjectNetwork n) (j : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i < j ∧ (i, j) ∈ N.P)

/-- Earliest event times, recursion (1) of Kelley–Walker (1959), p. 163, for durations `y`:
`t₀⁽⁰⁾ = 0` and `tⱼ⁽⁰⁾ = max [yᵢⱼ + tᵢ⁽⁰⁾ | i < j, (i, j) ∈ P]` for `1 ≤ j ≤ n`.
An event with no predecessor gets `0`; this covers the origin (`t₀⁽⁰⁾ = 0`), and for `j ≥ 1` it is
unreachable, because origin precedes every event (`ProjectNetwork.origin_precedes`). -/
noncomputable def earliest (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ
  | j =>
    if h : (preds N j).Nonempty then
      (preds N j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        (fun i => y i.1 j + earliest N y i.1)
    else 0
termination_by j => j.val
decreasing_by
  exact (Finset.mem_filter.mp i.2).2.1

end CriticalPath.CostCurve
