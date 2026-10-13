import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

open MeasureTheory

/-- The terminal value of (3.10), defined by its forward integral. -/
noncomputable def UT {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ≥0) (J₀ : Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  J₀ ω + ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), V s.toNNReal ω 

/-- The weighted Volterra integral in the corrected (3.12). -/
noncomputable def weightedTail {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Set.Ioc (t : ℝ) (T : ℝ),
    (r - (t : ℝ)) * V r.toNNReal ω 

end AntonelliBFSDE.NonsingularExample
