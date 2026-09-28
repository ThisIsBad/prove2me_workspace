import Mathlib

namespace LogRegretOCO.ONS

/-- Lemma 12 (Hazan–Agarwal–Kale 2007, p. 191). If `A ⪰ B ≻ 0` (i.e. `A − B` is positive
semidefinite and `B` is positive definite), then `A⁻¹ • (A − B) ≤ log(|A|/|B|)`, where
`C • E = Σ_{i,j} C_ij E_ij` is the entrywise (Frobenius) inner product and `|·|` the determinant. -/
theorem logdet_potential {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) := by sorry

end LogRegretOCO.ONS

