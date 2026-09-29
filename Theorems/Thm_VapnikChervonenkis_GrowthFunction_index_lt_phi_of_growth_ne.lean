import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 268, first display of the proof of Theorem 1: suppose
`m^S(r)` is not identically `2^r` and `n` is the first value of `r` for which `m^S(r) ≠ 2^r`
(`m^S(n) ≠ 2^n` and `m^S(r) = 2^r` for all `r < n`). Then for any sample `x_1, ···, x_r` of size
`r > n`, `Δ^S(x_1, ···, x_r) < Φ(n, r)`. -/
theorem index_lt_phi_of_growth_ne {X : Type*} (S : Set (Set X)) (n : ℕ)
    (hn : Shared.growthFunction S n ≠ 2 ^ n)
    (hmin : ∀ r < n, Shared.growthFunction S r = 2 ^ r) (r : ℕ) (hr : n < r) (x : Fin r → X) :
    Shared.index S x < Shared.Phi n r := by sorry

end VapnikChervonenkis.GrowthFunction

