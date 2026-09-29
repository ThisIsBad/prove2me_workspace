import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- The Lemma of the Appendix (pp. 28–29), carried over to the modified mechanism (proof of
Proposition 7, p. 30). Fix the announced preferences of all students other than `i` (they
are `P j`, `j ≠ i`), and compare the report `P i` with any other report `Qi`. At every
step `t` at whose beginning (the beginning of Step `t + 1`) student `i` still remains
under both reports, the remaining students, the school counters and the type-specific
counters (hence the remaining schools and which of them have room for which type) are
the same under both reports. -/
theorem ttcq_lemma_same_state {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (t : ℕ)
    (hi : i ∈ (run q qt τ pri P t).rem)
    (hi' : i ∈ (run q qt τ pri (Function.update P i Qi) t).rem) :
    (run q qt τ pri P t).rem = (run q qt τ pri (Function.update P i Qi) t).rem ∧
      (run q qt τ pri P t).cnt = (run q qt τ pri (Function.update P i Qi) t).cnt ∧
      (run q qt τ pri P t).tcnt = (run q qt τ pri (Function.update P i Qi) t).tcnt := by sorry

end SchoolChoice.TTCQuota

