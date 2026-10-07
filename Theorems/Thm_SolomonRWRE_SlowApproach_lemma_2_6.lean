import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology

namespace SolomonRWRE.SlowApproach

/-- Solomon, Lemma (2.6), p. 12. The transform of (2.5) differs from its comparison
series by `O(u)` as `u` decreases to zero. Formalization Note: the paper's `φ` is the
annealed transform `phi`; by Lemma (2.5) it equals `phiSeries` for every `n ≥ 1`, `u ≥ 0`,
so the statement is made on `phiSeries`. -/
theorem lemma_2_6 (γ θ : ℝ) (hθ : 1 < θ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcritical : 1 ≤ γ * θ) :
    (fun u => phiSeries γ θ u - psi γ θ u) =O[𝓝[>] (0 : ℝ)] (fun u => u) := by sorry

end SolomonRWRE.SlowApproach

