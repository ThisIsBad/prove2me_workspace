import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- The Lemma of the Appendix (pp. 28–29). Fix the announced preferences of all students
other than `i` (they are `P j`, `j ≠ i`), and compare the report `P i` with any other
report `Qi`. At every step `t` at whose beginning (the beginning of Step `t + 1`) student
`i` still remains under both reports, the remaining students and the remaining schools
are the same under both reports. -/
theorem ttc_lemma_same_state {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (t : ℕ)
    (hi : i ∈ (run q pri P t).rem)
    (hi' : i ∈ (run q pri (Function.update P i Qi) t).rem) :
    (run q pri P t).rem = (run q pri (Function.update P i Qi) t).rem ∧
      remSchools (run q pri P t) = remSchools (run q pri (Function.update P i Qi) t) := by sorry

end SchoolChoice.TTC

