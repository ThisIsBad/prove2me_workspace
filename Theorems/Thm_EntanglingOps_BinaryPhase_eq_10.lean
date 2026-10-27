import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eq. (10), p. 3: the resource state of the printed formula (10) is the gate `U(α)` of (9) on
`A₁B₁` applied to `|Φ⁺⟩_{A₁A₂}|Φ⁺⟩_{B₁B₂}` (entrywise, at `((a₁, a₂), (b₁, b₂))`), and the
operator `E_{A₁A₂,B₁B₂}` of Eq. (4) of the map `ρ ↦ U(α) ρ U(α)†` is `|ψ_α⟩⟨ψ_α|`. Stated for
every real `α` (the paper's `α_N` is one instance). -/
theorem eq_10 :
    (∀ (α : ℝ) (x : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)),
      resource α x = ∑ y : Fin 2 × Fin 2,
        gate α (x.1.1, x.2.1) y * phiPlus (y.1, x.1.2) * phiPlus (y.2, x.2.2)) ∧
    (∀ α : ℝ, choiOp (fun _ : Unit => gate α) = vecMulVec (resource α) (star (resource α))) := by sorry

end EntanglingOps.BinaryPhase

