import Definitions.Def_EthierKurtz_ComponentHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- C^{1,μ} with the component oscillation convention (1.13)–(1.14). -/
def COnceHolder {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (μ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiffOn ℝ 1 f D ∧ ∀ i : Fin d,
    ComponentHolder D μ (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))

end EthierKurtz
