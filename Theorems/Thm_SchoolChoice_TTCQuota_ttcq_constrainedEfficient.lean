import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- Proposition 6 (p. 23): the top trading cycles mechanism with type-specific quotas is
constrained efficient. For all capacities `q` with no shortage of seats, all type quotas
`qt`, all student types `τ`, all priorities and every announced preference profile `P`,
the outcome satisfies the controlled choice constraints (capacity and type quotas), and no
other assignment satisfying them makes every student weakly better off and some student
strictly better off under `P` (being unassigned is worse than every school). -/
theorem ttcq_constrainedEfficient {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) :
    IsConstrainedEfficient q qt τ P (ttcq q qt τ pri P) := by sorry

end SchoolChoice.TTCQuota

