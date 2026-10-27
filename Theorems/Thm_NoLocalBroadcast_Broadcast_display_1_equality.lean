import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Equality in (1), pp. 3–4: if `I(σ̃) = I({p_ij}) + Σ_{ij} p_{ij} I(ρ^{ij})`, then on the support
of `p` the reduction `ρ^{ij}_{A′}` does not depend on `j` and `ρ^{ij}_{B′}` does not depend on `i`. -/
theorem display_1_equality {ι κ a' b' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype a'] [DecidableEq a'] [Nonempty a'] [Fintype b'] [DecidableEq b']
    [Nonempty b']
    (p : ι × κ → ℝ) (hp0 : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1)
    (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ)
    (hρij : ∀ ij, QAlgorithms.IsDensityMatrix (ρij ij))
    (heq : mutualInfo (flaggedState p ρij) =
      mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ)) + ∑ ij, p ij * mutualInfo (ρij ij)) :
    (∀ i j j', 0 < p (i, j) → 0 < p (i, j') →
      QAlgorithms.traceRight (ρij (i, j)) = QAlgorithms.traceRight (ρij (i, j'))) ∧
    (∀ i i' j, 0 < p (i, j) → 0 < p (i', j) →
      QAlgorithms.traceLeft (ρij (i, j)) = QAlgorithms.traceLeft (ρij (i', j))) := by sorry

end NoLocalBroadcast.Broadcast

