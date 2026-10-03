import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel

namespace ProcessingNetworks.ProportionalFairness

/-- Lemma 10.15, Dai & Harrison p. 204 (PDF p. 220): let `t > 0` be a regular point of `(D,Z)`,
and assume `Ḋ_i(t) > 0` for every class `i` with `Z_i(t) > 0`. Then `Ḋ_i(t) > 0` for *every*
class `i` (Eq. 10.70) — positivity propagates from occupied classes to all classes via the
routing structure's connectivity (Lemma B.9), not merely tautologically restated on the occupied
classes themselves. -/
theorem departure_rate_positivity_propagates
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t)
    (hpos : ∀ i, 0 < Zh t i → 0 < deriv (fun s => Dh s i) t) :
    ∀ i, 0 < deriv (fun s => Dh s i) t := by sorry

end ProcessingNetworks.ProportionalFairness
