import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped ComplexOrder

/-- Eq. (12), p. 3, with the probability sentence and the communication sentence: for `N ≥ 1` and
every density matrix `ρ` on `A₃B₃`, the paper's step `k` is performed with probability
`(1/2)^{k−1}` (`1 ≤ k ≤ N`), the average entanglement is
`Ē[U(α_N)] = ∑_{k=1}^N (1/2)^{k−1} E(ψ_{α_{N−k+1}})`, and the average communication in each
direction (steps `1, …, N − 1`) is `2 − (1/2)^{N−2}` bits; and
`∑_{k=1}^N (1/2)^{k−1} E(ψ_{α_{N−k+1}}) = α_N f_N`. -/
theorem eq_12 (N : ℕ) (hN : 1 ≤ N) :
    (∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 →
      (∀ k ∈ Finset.Icc 1 N, reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1)) ∧
      avgEnt N ρ = ∑ k ∈ Finset.Icc 1 N,
        (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) ∧
      avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2)) ∧
    ∑ k ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) =
      alphaN N * fN N := by sorry

end EntanglingOps.BinaryPhase

