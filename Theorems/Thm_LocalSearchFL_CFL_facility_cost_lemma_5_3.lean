import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

/-- **Lemma 5.3 (facility cost)**, p. 559: the facility cost of a locally optimum CFL solution
`X` (at least one client) satisfies `cost_f(X) ≤ 3 · cost_f(O) + 2 · cost_s(O)` for every CFL
solution `O`. -/
theorem facility_cost_lemma_5_3 {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costF f X ≤ 3 * costF f O + 2 * costS I O := by sorry

end LocalSearchFL.CFL

