import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_BNCovPack_Packing_Scheme

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- Buchbinder–Naor 2009, proof of Theorem 3.1, claim (ii) (p. 5; proved p. 6): after every round
`r`, the primal solution `x` maintained by the scheme is feasible for the covering constraints
given so far (`x ≥ 0` and `∑ᵢ a(i,k) x(i) ≥ 1` for every column `k < r`), and no primal variable
ever decreases from one round to the next. -/
theorem claim_ii {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    (∀ r : ℕ, r ≤ m →
      (∀ i, 0 ≤ (stateAfter inst B r).x i) ∧
      (∀ k : Fin m, (k : ℕ) < r → 1 ≤ ∑ i, inst.a i k * (stateAfter inst B r).x i)) ∧
    (∀ r : ℕ, ∀ i, (stateAfter inst B r).x i ≤ (stateAfter inst B (r + 1)).x i) := by sorry

end BNCovPack.Packing

