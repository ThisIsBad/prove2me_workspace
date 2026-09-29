import Definitions.Def_EthierKurtz_ComponentHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- C^{2,μ} on an open set; ordered second partials cover the multiindices
of order two in (1.14). Values outside the open set are immaterial. -/
def CTwiceHolder {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (μ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiffOn ℝ 2 f Ω ∧ ∀ i j : Fin d,
    ComponentHolder Ω μ (fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1))

end EthierKurtz
