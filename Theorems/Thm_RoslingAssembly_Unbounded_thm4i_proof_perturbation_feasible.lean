import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model
import Definitions.Def_RoslingAssembly_Unbounded_Perturb

namespace RoslingAssembly.Unbounded

open MeasureTheory

/-- Proof of Theorem 4(i), p. 578: ordering `δ ≥ 0` more units of every item of the subsystem
`{i} ∪ B(i)`, timed so that each extra unit arrives when its successor orders its own extra unit,
and holding them forever, preserves measurability and feasibility (3). -/
theorem thm4i_proof_perturbation_feasible (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : RoslingAssembly.SeriesEquiv.Policy) (hπm : IsMeasurablePolicy π) (hπ : S.Feasible x0 π) :
    IsMeasurablePolicy (S.perturb π i δ) ∧ S.Feasible x0 (S.perturb π i δ) := by sorry

end RoslingAssembly.Unbounded

