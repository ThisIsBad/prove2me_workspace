import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.8, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, there is a
constant `M > 0` such that the upper-right Dini derivative `D⁺φ(t) ≤ M` for every `t ≥ 0`
(Eq. 10.40). -/
theorem entropy_lyapunov_dini_bounded
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → diniUpperRight (phi Dh Zh alpha) t ≤ (M : EReal) := by sorry

end ProcessingNetworks.ProportionalFairness

