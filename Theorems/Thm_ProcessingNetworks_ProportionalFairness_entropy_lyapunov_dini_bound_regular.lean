import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.9, Dai & Harrison p. 197 (PDF p. 213): for a PF fluid model solution, at each
regular point `t > 0`, the upper-right Dini derivative of `φ` is bounded by
`∑_i Ż_i(t) log(Ḋ_i(t)/α_i)` (Eq. 10.41). -/
theorem entropy_lyapunov_dini_bound_regular
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0)) (alpha : Fin I → ℝ)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t) :
    diniUpperRight (phi Dh Zh alpha) t ≤
      ((∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) : ℝ) :
        EReal) := by sorry

end ProcessingNetworks.ProportionalFairness

