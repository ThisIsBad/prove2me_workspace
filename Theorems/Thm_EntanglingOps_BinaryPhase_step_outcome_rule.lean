import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker ComplexOrder

/-- p. 3, the step-outcome rule: with the resource `|ψ_β⟩`, each of the 16 Bell outcomes
`(i, j)` (Alice's on `A₂A₃`, Bob's on `B₂B₃`), followed by the corrections `σ_i` on `A₁` and
`σ_j` on `B₁`, acts on `A₃B₃ → A₁B₁` as `c · U(β)` if `i₁ = j₁` and `c · U(−β)` if `i₁ ≠ j₁`,
with `|c|² = 1/16`; `U(β)† = U(−β)`; and every outcome has probability `1/16` on every input
density matrix. Stated for every real `β` (the paper's step uses `β = α_N`). -/
theorem step_outcome_rule :
    (∀ (β : ℝ) (i j : Fin 2 × Fin 2), ∃ c : ℂ, Complex.normSq c = 1 / 16 ∧
        stepKraus β i j = c • gate (if i.1 = j.1 then β else -β)) ∧
    (∀ β : ℝ, (gate β)ᴴ = gate (-β)) ∧
    (∀ (β : ℝ) (i j : Fin 2 × Fin 2) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
        ρ.PosSemidef → ρ.trace = 1 →
        (Matrix.trace (stepKraus β i j * ρ * (stepKraus β i j)ᴴ)).re = 1 / 16) := by sorry

end EntanglingOps.BinaryPhase

