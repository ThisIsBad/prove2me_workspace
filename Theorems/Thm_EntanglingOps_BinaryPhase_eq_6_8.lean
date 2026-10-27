import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eqs. (8) and (6), p. 2: a completely positive map `ℰ(ρ) = ∑_k O_k ρ O_k†` on `A₁B₁` is
recovered from its operator `E = choiOp O` of Eq. (4):
(8) `ℰ(ρ_{A₁B₁}) = d² tr_{A₂B₂}(E_{A₁A₂,B₁B₂} ρ^T_{A₂B₂})`, on the carrier `((a₁, b₁), (a₂, b₂))`;
(6) `ℰ(ρ_{A₁B₁}) = d⁴ tr_{A₂A₃B₂B₃}(E_{A₁A₂,B₁B₂} ρ_{A₃B₃} P_{A₂A₃} P_{B₂B₃})`, on the carrier
`((a₁, b₁), ((a₂, b₂), (a₃, b₃)))`. In both, `ρ` on the right is the same matrix as on the left,
placed on `A₂B₂` (transposed) or `A₃B₃`. Stated for every matrix `ρ`. -/
theorem eq_6_8 (d : ℕ) (hd : 0 < d) {κ : Type} [Fintype κ]
    (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    krausMap O ρ = ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
        (reindex (regroup d) (regroup d) (choiOp O) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρᵀ)) ∧
    krausMap O ρ = ((d : ℂ) ^ 4) • WildeQIT.partialTraceRight
        (reindex (Equiv.prodAssoc (Fin d × Fin d) (Fin d × Fin d) (Fin d × Fin d))
            (Equiv.prodAssoc (Fin d × Fin d) (Fin d × Fin d) (Fin d × Fin d))
            (reindex (regroup d) (regroup d) (choiOp O) ⊗ₖ
              (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) *
          ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
            (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d))) := by sorry

end EntanglingOps.BinaryPhase

