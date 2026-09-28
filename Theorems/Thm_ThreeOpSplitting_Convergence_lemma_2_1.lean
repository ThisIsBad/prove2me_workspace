import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

namespace ThreeOpSplitting.Convergence

/-- Davis–Yin, Lemma 2.1 (p. 832): the points of Fig. 1 and the identities for `T`. -/
theorem lemma_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ : ℝ) (JA JB : H → H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ : 0 < γ)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB) (z : H) :
    let xB := JB z
    let z' := (2 : ℝ) • xB - z
    let z'' := z' - γ • C xB
    let xA := JA z''
    let uB := γ⁻¹ • (z - xB)
    let uA := γ⁻¹ • (z'' - xA)
    uB ∈ B xB ∧ uA ∈ A xA ∧
      threeOp γ JA JB C z - z = xA - xB ∧
      xA - xB = -(γ • (uB + uA + C xB)) ∧
      threeOp γ JA JB C z = xA + γ • uB := by sorry

end ThreeOpSplitting.Convergence

