import Mathlib
import Definitions.Def_SchoolChoice_TTC_Model
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Proposition 3 (p. 17): the top trading cycles mechanism is Pareto efficient. For all
capacities with no shortage of seats, all priorities and every announced profile `P`, the
mechanism assigns every student a school, the assignment is a matching, and it is Pareto
efficient with respect to `P`. -/
theorem ttc_paretoEfficient {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) :
    ∃ μ : I → S, (∀ i, ttc q pri P i = some (μ i)) ∧ IsMatching q μ ∧
      IsParetoEfficient q P μ := by sorry

end SchoolChoice.TTC

