import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 265, Subsection 1: "Obviously, `Δ^S(x_1, ···, x_r)` is
always at most `2^r`." -/
theorem index_le_two_pow {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := by sorry

end VapnikChervonenkis.GrowthFunction
