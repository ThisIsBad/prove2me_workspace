import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_GlobalStability_UnidirectionalRing
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel

namespace ProcessingNetworks.GlobalStability

/-- Theorem 8.24, Dai & Harrison p. 152 (PDF p. 168): if a unidirectional ring network satisfies
the standard load condition `ρ < e` (`ρ := W(λ)`, `e` the vector of ones), then its fluid model
is globally stable. The arrival rates are nonnegative and the mean service times positive, as
for every queueing network of Section 2.6. -/
theorem ring_globally_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I))
    (hring : IsUnidirectionalRing dat succ)
    (hlam : ∀ i, 0 ≤ dat.lam i) (hm : ∀ i, 0 < dat.m i)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    FluidModelGloballyStable dat := by sorry

end ProcessingNetworks.GlobalStability

