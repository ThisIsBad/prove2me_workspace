import Mathlib
import Definitions.Def_TeschlODE_Shared_IsChaotic
import Definitions.Def_TeschlODE_IntervalMaps_SensitiveDependence

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.3, p. 297: if `f : M → M` on a metric space `M` is chaotic (continuous,
`M` infinite, topologically transitive, periodic points dense; p. 296), then it exhibits
sensitive dependence on initial conditions (pp. 295–296). -/
theorem chaotic_sensitiveDependence {M : Type*} [MetricSpace M] (f : M → M)
    (hf : TeschlODE.Shared.IsChaotic f) : SensitiveDependence f := by sorry

end TeschlODE.IntervalMaps

