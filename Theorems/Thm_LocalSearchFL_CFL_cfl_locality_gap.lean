import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Theorem 5.5**, p. 560: local search for the metric capacitated facility location problem
(with multiple copies of a facility allowed), where each step either adds a copy of a facility
or deletes a subset of the open copies and adds multiple copies of one facility (neighbourhood
(9)), has locality gap at most 4: for every instance with at least one client, every locally
optimum solution `X` and every solution `O`, `cost(X) ≤ 4 · cost(O)`. -/
theorem cfl_locality_gap {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    cost I f X ≤ 4 * cost I f O := by sorry

end LocalSearchFL.CFL

