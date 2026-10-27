import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eq. (7), p. 2: `d² tr_{A₃B₃}(ρ_{A₃B₃} P_{A₂A₃} P_{B₂B₃}) = ρ^T_{A₂B₂}`. The carrier is indexed
`((a₂, b₂), (a₃, b₃))`; `ρ_{A₃B₃}` is `𝟙_{A₂B₂} ⊗ ρ`, `P_{A₂A₃} P_{B₂B₃}` is `projPhiPair d`,
`tr_{A₃B₃}` is `partialTraceRight`, and `ρᵀ` is the transpose in the product basis
`S_{A₂} ⊗ S_{B₂}`. Stated for every matrix `ρ`. -/
theorem eq_7 (d : ℕ) (hd : 0 < d) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
      (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d) = ρᵀ := by sorry

end EntanglingOps.BinaryPhase

