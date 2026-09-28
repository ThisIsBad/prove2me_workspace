import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Section II.B (p. 15): at every step of the top trading cycles algorithm at which some
student remains, there is at least one cycle, i.e. some remaining student is in a cycle.
`run q pri P t` is the state at the beginning of Step `t + 1`. -/
theorem ttc_exists_cycle {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (t : ℕ)
    (hrem : (run q pri P t).rem.Nonempty) :
    ∃ i ∈ (run q pri P t).rem, InCycle P pri (run q pri P t) i := by sorry

end SchoolChoice.TTC

