import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- **Theorem 1** of Vapnik and Chervonenkis (1971), p. 267: the growth function `m^S(r)` is
either identically equal to `2^r`, or else it is majorized by `r^n + 1`, where `n` is a positive
constant equal to the first value of `r` for which `m^S(r) = 2^r` is violated. The class `S` is
assumed nonempty (for `S = ∅` the first violation is `r = 0`, and `n` is not positive). -/
theorem theorem1_growth_dichotomy {X : Type*} (S : Set (Set X)) (hS : S.Nonempty) :
    (∀ r : ℕ, Shared.growthFunction S r = 2 ^ r) ∨
      ∃ n : ℕ, 0 < n ∧ Shared.growthFunction S n ≠ 2 ^ n ∧
        (∀ r < n, Shared.growthFunction S r = 2 ^ r) ∧
        ∀ r : ℕ, Shared.growthFunction S r ≤ r ^ n + 1 := by sorry

end VapnikChervonenkis.GrowthFunction

