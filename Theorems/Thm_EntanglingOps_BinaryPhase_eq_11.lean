import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- Eq. (11), p. 3: the entropy of entanglement (bits) of `|ψ_α⟩` across `(A₁A₂)|(B₁B₂)` is the
binary entropy of `x = cos² α`; `E(ψ_{α₂}) = 1`, `E(ψ_{α₁}) = 0`; and
`U(π/2) = −i σ_x ⊗ σ_x`. The first identity is stated for every real `α`. -/
theorem eq_11 :
    (∀ α : ℝ, entEntropy (resource α) = WildeQIT.binaryEntropy (Real.cos α ^ 2)) ∧
    entEntropy (resource (alphaN 2)) = 1 ∧
    entEntropy (resource (alphaN 1)) = 0 ∧
    gate (Real.pi / 2) = (-Complex.I) • (sx ⊗ₖ sx) := by sorry

end EntanglingOps.BinaryPhase

