import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The mean vector of a probability measure `Q` on `ℝ^m`, `E_Q[ξ]`, used throughout Kuhn et
al. 2019. Redefined locally in this chapter's own namespace, matching `02-gelbrich`'s
definition of the same name: `02-gelbrich` is not yet a published mission, so a draft item
cannot import another draft (`CAPTAIN_ADDENDUM_WAVE2.md`, rule 5). -/
noncomputable def meanVector {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin m) :=
  ∫ x, x ∂Q

end WassersteinDRO.Guarantees
