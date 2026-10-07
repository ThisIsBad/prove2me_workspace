import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_ProjectionBasics

namespace BoydADMM.Nonconvex

/-- §9.1, p. 74: any choice of the `min c n` largest-magnitude coordinates
gives a nearest point of the cardinality-constrained set. -/
theorem cardinality_projection {n : ℕ} (v : Fin n → ℝ) (c : ℕ)
    (I : Finset (Fin n))
    (hcard : I.card = min c n)
    (hlargest : ∀ i ∈ I, ∀ j ∉ I, |v j| ≤ |v i|) :
    restrictTo I v ∈ sparseSet c ∧
    ∀ x ∈ sparseSet c, sqDist (restrictTo I v) v ≤ sqDist x v := by sorry

end BoydADMM.Nonconvex

