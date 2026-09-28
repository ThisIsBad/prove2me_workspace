import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm
import Definitions.Def_SchoolChoice_TTC_SerialDictatorship

namespace SchoolChoice.TTC

/-- Section II.B (p. 16): when all schools have the same priority ordering `π`, the top
trading cycles mechanism reduces to the serial dictatorship induced by `π`. -/
theorem ttc_eq_serialDictatorship {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (π : Priority I) (pri : S → Priority I) (hpri : ∀ s, pri s = π) (P : I → Pref S) :
    ttc q pri P = serialDictatorship q π P := by sorry

end SchoolChoice.TTC

