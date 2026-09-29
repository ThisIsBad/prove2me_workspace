import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **(4.1)** (Ogryczak–Ruszczyński 2002, §4, p. 69). For integrable `X`, `Y`:
`X ⪰_SSD Y ⇒ μ_X ≥ μ_Y`. -/
theorem mean_le_of_ssd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    Shared.SSD P X Y → mean P Y ≤ mean P X := by sorry

end DualSSD.MeanRisk
