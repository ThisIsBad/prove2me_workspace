import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- Proposition 7 (p. 23): the top trading cycles mechanism with type-specific quotas is
strategy-proof. For all capacities `q` with no shortage of seats, all type quotas `qt`,
all student types `τ`, all priorities, every profile of announced preferences `P`, every
student `i` whose true preference is `P i`, and every alternative report `Qi` (the
others' reports unchanged): if `i` is assigned a school `s'` when reporting `Qi`, then
she is assigned a school `s` when reporting `P i`, and she weakly prefers `s` to `s'`
under `P i` (rank `0` is the favourite). -/
theorem ttcq_strategyProof {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (s' : S)
    (hs' : ttcq q qt τ pri (Function.update P i Qi) i = some s') :
    ∃ s : S, ttcq q qt τ pri P i = some s ∧ P i s ≤ P i s' := by sorry

end SchoolChoice.TTCQuota

