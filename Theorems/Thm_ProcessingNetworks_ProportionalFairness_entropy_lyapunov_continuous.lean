import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.7, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, the entropy
Lyapunov function `φ` is continuous on `(0,∞)`. Not in `BRIEF.md`'s disposition table for this
chunk (a planning-time omission, on the same page as Lemmas 10.6/10.8/10.9 and explicitly one of
the "following five lemmas" the book says suffice to prove Theorem 10.5); added here and
documented in `HARD.md`/`STATUS.md`, per this series' established convention for such omissions
(cf. missions VI/VII's Lemma 8.20). -/
theorem entropy_lyapunov_continuous
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i) :
    ContinuousOn (phi Dh Zh alpha) (Set.Ioi 0) := by sorry

end ProcessingNetworks.ProportionalFairness

