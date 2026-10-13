import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Proposition 7.49** (Jankov–von Neumann theorem, p. 182). Let `X`, `Y` be Borel spaces and
`A ⊆ X × Y` analytic. There is an analytically measurable `φ : proj_X(A) → Y` whose graph lies
in `A`. -/
theorem jankov_von_neumann {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (A : Set (X × Y)) (hA : AnalyticSet A) :
    ∃ φ : (Prod.fst '' A) → Y,
      IsAnalyticallyMeasurableFun (Prod.fst '' A) φ ∧ ∀ x : Prod.fst '' A, ((x : X), φ x) ∈ A := by sorry

end BertsekasShreve.AnalyticSelection

