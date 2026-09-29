import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_maxNorm
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

namespace HighDimStat.RandomMatrices

/-- **Eq. (6.54)** (deterministic thresholding bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 181. For any `λn` such that `‖Σ̂-Σ‖_max ≤ λn`, the thresholded matrix satisfies
`|||Tλn(Σ̂)-Σ|||₂ ≤ 2|||A|||₂λn`, where `A` is the adjacency matrix of `Σ`'s sparsity pattern. -/
theorem thresholding_deterministic_bound {d : ℕ} (SigHat Sig : Matrix (Fin d) (Fin d) ℝ)
    (lam : ℝ) (hmax : maxNorm (SigHat - Sig) ≤ lam) :
    opNorm (thresholdMatrix lam SigHat - Sig) ≤ 2 * opNorm (adjacencyMatrix Sig) * lam := by sorry

end HighDimStat.RandomMatrices
