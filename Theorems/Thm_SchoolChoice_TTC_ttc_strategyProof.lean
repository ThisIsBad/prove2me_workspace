import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Proposition 4 (p. 17): the top trading cycles mechanism is strategy-proof. For all
capacities with no shortage of seats, all priorities, every profile of announced
preferences `P`, every student `i` whose true preference is `P i`, and every alternative
report `Qi`, student `i` is assigned a school `s` when reporting `P i` and a school `s'`
when reporting `Qi` (the others' reports unchanged), and she weakly prefers `s` to `s'`
under `P i` (rank `0` is the favourite). -/
theorem ttc_strategyProof {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) :
    ∃ s s' : S, ttc q pri P i = some s ∧
      ttc q pri (Function.update P i Qi) i = some s' ∧ P i s ≤ P i s' := by sorry

end SchoolChoice.TTC

