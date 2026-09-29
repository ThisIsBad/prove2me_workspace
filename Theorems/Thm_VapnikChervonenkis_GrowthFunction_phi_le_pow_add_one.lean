import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 266: "For `n > 0` and `r ≧ 0`, `Φ(n, r) ≦ r^n + 1`." -/
theorem phi_le_pow_add_one (n r : ℕ) (hn : 0 < n) :
    Shared.Phi n r ≤ r ^ n + 1 := by sorry

end VapnikChervonenkis.GrowthFunction
