import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem exchange_inequality (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (r : ℕ) (z : State)
    (i j : ℕ) (hi : i < z.n) (hj : j < z.n) (hXi : 1 ≤ z.X i) (hXj : 1 ≤ z.X j)
    (hwi : WellFormed P (evict z i)) (hwj : WellFormed P (evict z j))
    (hcap : ∑ l ∈ Finset.range z.n, z.X l = P.C + 1)
    (hscore : score P z i < score P z j) :
    optValue P r (evict z i) ≤ optValue P r (evict z j) := by sorry

end TailOptCaching.ETLRU

