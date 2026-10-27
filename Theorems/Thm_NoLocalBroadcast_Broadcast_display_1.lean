import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Display (1), p. 3: for `σ̃ = Σ_{ij} p_{ij} |i⟩⟨i| ⊗ |j⟩⟨j| ⊗ ρ^{ij}` (cut `AA′ : BB′`),
`I(σ̃) = I({p_ij}) + Σ_i p_i^A S(τ^i_{A′}) + Σ_j p_j^B S(τ^j_{B′}) − Σ_{ij} p_{ij} S(ρ^{ij})`
and `I(σ̃) ≥ I({p_ij}) + Σ_{ij} p_{ij} I(ρ^{ij})`, where `I({p_ij})` is the mutual information
of the diagonal state of `p`. -/
theorem display_1 {ι κ a' b' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype a'] [DecidableEq a'] [Nonempty a'] [Fintype b'] [DecidableEq b'] [Nonempty b']
    (p : ι × κ → ℝ) (hp0 : ∀ ij, 0 ≤ p ij) (hp1 : ∑ ij, p ij = 1)
    (ρij : ι × κ → Matrix (a' × b') (a' × b') ℂ)
    (hρij : ∀ ij, QAlgorithms.IsDensityMatrix (ρij ij)) :
    mutualInfo (flaggedState p ρij) =
        mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ))
          + ∑ i, (∑ j, p (i, j)) * QAlgorithms.vnEntropy
              (∑ j, ((p (i, j) / ∑ j', p (i, j') : ℝ) : ℂ) • QAlgorithms.traceRight (ρij (i, j)))
          + ∑ j, (∑ i, p (i, j)) * QAlgorithms.vnEntropy
              (∑ i, ((p (i, j) / ∑ i', p (i', j) : ℝ) : ℂ) • QAlgorithms.traceLeft (ρij (i, j)))
          - ∑ ij, p ij * QAlgorithms.vnEntropy (ρij ij) ∧
    mutualInfo (Matrix.diagonal fun ij => (p ij : ℂ)) + ∑ ij, p ij * mutualInfo (ρij ij)
      ≤ mutualInfo (flaggedState p ρij) := by sorry

end NoLocalBroadcast.Broadcast

