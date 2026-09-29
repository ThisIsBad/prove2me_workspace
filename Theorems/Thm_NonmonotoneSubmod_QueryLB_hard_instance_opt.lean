import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

namespace NonmonotoneSubmod.QueryLB

/-- §4.2, proof of Theorem 4.5 (pp. 1149–1150, third bullet): the maximum of `f_C` is
`OPT = ½n²(1 − 2ϵ + 2ϵ²) = n²/2 − mn + m²` (`m = ϵn`), attained at `S = C`
(`k = n/2`, `ℓ = 0`). -/
theorem hard_instance_opt (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (C : Finset (Fin n)) (hC : C.card = n / 2) :
    NonmonotoneSubmod.Shared.OPT (fC n m C) = (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 ∧
      fC n m C C = NonmonotoneSubmod.Shared.OPT (fC n m C) := by sorry

end NonmonotoneSubmod.QueryLB
