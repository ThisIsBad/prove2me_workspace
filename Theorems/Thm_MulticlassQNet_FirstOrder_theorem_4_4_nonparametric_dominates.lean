import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Constraints

namespace MulticlassQNet.FirstOrder

/-- Theorem 4.4 (p. 21): nonnegative variables `x`, `I`, `Nv` satisfying the
equalities (24), (25) of Theorem 4.2 and (28) of Theorem 4.3 satisfy every inequality (18) of
Theorem 4.1, in product form. -/
theorem theorem_4_4_nonparametric_dominates {N R : ℕ} (net : Network N R) (lam : Fin R → ℝ)
    (htraffic : net.IsTrafficSolution lam) (hopen : net.IsOpen) (hload : net.LoadLtOne lam)
    (x : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ)
    (hx : ∀ r, 0 ≤ x r) (hI : ∀ r r', 0 ≤ I r r') (hNv : ∀ i r', 0 ≤ Nv i r')
    (h24 : net.Eq24 lam (fun r => lam r * x r) I)
    (h25 : net.Eq25 lam (fun r => lam r * x r) I)
    (h28 : net.Eq28 (fun r => lam r * x r) I Nv) :
    ∀ (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ),
      net.FCondition S f fi → (∀ r ∈ S, 0 ≤ f r) →
        net.Nprime lam S f ≤ net.Dprime S f fi * ∑ r ∈ S, f r * (lam r * x r) := by sorry

end MulticlassQNet.FirstOrder

