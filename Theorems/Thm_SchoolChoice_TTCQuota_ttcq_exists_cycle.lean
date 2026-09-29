import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- Section III.B, Step 1 (p. 22): "There is at least one cycle." At every step of the top
trading cycles algorithm with type-specific quotas, once the stuck students (those with no
remaining school that has room for their type) have been removed, if some student still
remains then some remaining student is in a cycle. `run … t` is the state at the
beginning of Step `t + 1` and `prune τ (run … t)` the state after the stuck removal. -/
theorem ttcq_exists_cycle {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (t : ℕ)
    (hrem : (prune τ (run q qt τ pri P t)).rem.Nonempty) :
    ∃ i ∈ (prune τ (run q qt τ pri P t)).rem,
      InCycle P pri τ (prune τ (run q qt τ pri P t)) i := by sorry

end SchoolChoice.TTCQuota

