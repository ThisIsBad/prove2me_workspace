import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMax
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMin
import Definitions.Def_BNCovPack_Packing_Scheme

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- Buchbinder–Naor 2009, proof of Theorem 3.1, claim (iii) (p. 5; proved p. 6): when the scheme
has processed all `m` columns, every packing constraint `i` is violated by at most a factor
`2 log(1 + n aᵢ(max)/aᵢ(min))/B`:
`∑_{k=1}^{m} a(i,k) y(k) ≤ c(i) · 2 log(1 + n aᵢ(max)/aᵢ(min)) / B`,
with `n = |I|`, `aᵢ(max)` the largest and `aᵢ(min)` the smallest non-zero coefficient of `x(i)`
over all `m` columns, and the natural logarithm. -/
theorem claim_iii {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} [NeZero m]
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ i : I, ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k ≤
      inst.c i * (2 * Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i)) / B := by sorry

end BNCovPack.Packing

