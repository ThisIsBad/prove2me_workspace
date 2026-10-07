import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- The first row of B⁻¹, the pricing multipliers, and the current N̄ column, pp. 852, 854–855. -/
theorem bordered_inverse_first_row {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsUnit (basisMat I β).det) :
    (bordered I β)⁻¹ =
      Matrix.fromBlocks 1
        (Matrix.of fun _ r => (Matrix.vecMul (costRow I β) (basisMat I β)⁻¹) r)
        0 (basisMat I β)⁻¹ ∧
    mult I β = Matrix.vecMul (costRow I β) (basisMat I β)⁻¹ ∧
    (∀ j : Col I, priceOut I β j =
      (∑ i, mult I β i * colVec I j i) - colCost I j) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    (∀ i, ((basicSol I β).sum fun j v => colVec I j i * v) = (I.N i : ℝ)) := by sorry

end GilmoreGomory61.CuttingStock

