import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model

namespace RoslingAssembly.Unbounded

open MeasureTheory

/-- Theorem 4(i), p. 574: if `h_i α^{−M_{s(i)}} + ∑_{k ∈ B(i)} h_k α^{−M_{s(k)}} < 0` for some
item `i`, then the minimal cost of Problem P is unbounded below: for every real `C` there is a
measurable policy, feasible from `x0`, whose cost is a real number below `C`. -/
theorem theorem4i_cost_unbounded_below (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (hneg : S.echelonSum i < 0) :
    ∀ C : ℝ, ∃ π : RoslingAssembly.SeriesEquiv.Policy, IsMeasurablePolicy π ∧ S.Feasible x0 π ∧
      ∃ r : ℝ, S.cost π = (r : EReal) ∧ r < C := by sorry

end RoslingAssembly.Unbounded

