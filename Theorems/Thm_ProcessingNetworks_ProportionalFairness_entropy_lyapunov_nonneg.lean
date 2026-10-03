import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.6, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, the entropy
Lyapunov function `φ(t) ≥ 0` for every `t ≥ 0`, and `Z(t) ≠ 0` implies `φ(t) > 0`. -/
theorem entropy_lyapunov_nonneg
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ phi Dh Zh alpha t ∧ (Zh t ≠ 0 → 0 < phi Dh Zh alpha t) := by sorry

end ProcessingNetworks.ProportionalFairness
