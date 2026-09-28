import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Section II.B (p. 16): the algorithm terminates within `card I` steps — after
`card I` steps no student remains — and the resulting assignment is a matching:
every student is assigned some school and no school receives more students than its
capacity. -/
theorem ttc_terminates {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) :
    (run q pri P (Fintype.card I)).rem = ∅ ∧
      ∃ μ : I → S, (∀ i, ttc q pri P i = some (μ i)) ∧ IsMatching q μ := by sorry

end SchoolChoice.TTC

