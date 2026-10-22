import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.11, Dai & Harrison p. 197 (PDF p. 213): given that the load condition (10.37) holds,
there is `ε > 0` such that, for each regular point `t > 0` with `Z(t) ≠ 0`, the entropy drift
`∑_i Ż_i(t) log(Ḋ_i(t)/α_i) ≤ -ε` (Eq. 10.42). -/
theorem entropy_lyapunov_drift_bound
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (hload : ∃ a ∈ dat.TildeAllocSet,
      ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ), IsPFFluidModelSolution dat Ah Dh Th Zh →
        ∀ t : ℝ, 0 < t → RegularPoint Ah Dh Th Zh t → Zh t ≠ 0 →
          ∑ i, deriv (fun s => Zh s i) t * Real.log (deriv (fun s => Dh s i) t / alpha i) ≤ -ε := by sorry

end ProcessingNetworks.ProportionalFairness

