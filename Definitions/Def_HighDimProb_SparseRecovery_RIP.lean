import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_HighDimProb_SparseRecovery_Sparsity

namespace HighDimProb.SparseRecovery

/-- **`SatisfiesRIP A α β s`**: the `m × n` matrix `A` satisfies the **restricted isometry
property (RIP)** with parameters `α, β, s`. Vershynin, *High-Dimensional Probability* (2018),
Definition 10.5.8, p. 260 (PDF p. 268): "An `m × n` matrix `A` satisfies the restricted isometry
property (RIP) with parameters `α`, `β` and `s` if the inequality `α‖v‖₂ ≤ ‖Av‖₂ ≤ β‖v‖₂` holds
for all vectors `v ∈ ℝⁿ` such that `‖v‖₀ ≤ s`." Direct transcription: `A.mulVec v` is `Av`,
`l2Norm` is `‖·‖₂`, `IsSSparse v s` is `‖v‖₀ ≤ s`. -/
def SatisfiesRIP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β s : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, IsSSparse v s →
    α * l2Norm v ≤ l2Norm (A.mulVec v) ∧ l2Norm (A.mulVec v) ≤ β * l2Norm v

end HighDimProb.SparseRecovery
