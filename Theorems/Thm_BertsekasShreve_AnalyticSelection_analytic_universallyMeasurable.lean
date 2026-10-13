import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Corollary 7.42.1** (p. 169). In a Borel space every analytic set is universally
measurable. -/
theorem analytic_universallyMeasurable {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    (A : Set X) (hA : AnalyticSet A) : IsUniversallyMeasurable A := by sorry

end BertsekasShreve.AnalyticSelection

