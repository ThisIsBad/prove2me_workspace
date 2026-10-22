import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_BNCovPack_Packing_Scheme

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- Buchbinder–Naor 2009, proof of Theorem 3.1, claim (i) (p. 5; proved pp. 5–6): in each round
`r`, the value `X` of the primal solution maintained by the online fractional packing scheme is
at most `B` times the value `Y` of its dual solution, `Y(r) ≥ X(r)/B`. -/
theorem claim_i {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ r : ℕ, r ≤ m → primalValue inst B r ≤ B * dualValue inst B r := by sorry

end BNCovPack.Packing

