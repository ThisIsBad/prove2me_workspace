import Mathlib

namespace LogRegretOCO.FTAL
theorem logdet_potential {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) := by sorry
end LogRegretOCO.FTAL

