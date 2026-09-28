import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The covariance matrix of a probability measure `Q` on `ℝ^m`,
`E_Q[(ξ-E_Q[ξ])(ξ-E_Q[ξ])^T]`. Redefined locally in this chapter's own namespace; see
`Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def covarianceMatrix {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m))) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun i j => ∫ x : EuclideanSpace ℝ (Fin m), (x i - meanVector Q i) * (x j - meanVector Q j) ∂Q)

end WassersteinDRO.Guarantees
