import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- The ordering `ι` of p. 24 exists for every number of jobs `n ≠ 2`: a bijection from ordered
pairs of distinct jobs onto the machines `2, …, n(n−1)+1` such that no `ι(j,ℓ)` equals
`ι(ℓ,k) + 1`. (For `n = 2` no such ordering exists; the paper says it "can easily be
constructed" without excluding this case.) -/
theorem iota_exists (n : ℕ) (hn : n ≠ 2) : ∃ ι : Fin n → Fin n → ℕ, Admissible n ι := by sorry

end SchedComplexity.NoWait

