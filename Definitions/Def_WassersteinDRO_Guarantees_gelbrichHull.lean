import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_meanVector
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_WassersteinDRO_Guarantees_meanCovarianceUncertaintySet

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The Gelbrich hull `G_ε(µ̂,Ŝ)`, Kuhn et al. 2019, Definition 2, p. 17. Redefined locally
in this chapter's own namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
def gelbrichHull {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧
    (meanVector Q, covarianceMatrix Q) ∈ meanCovarianceUncertaintySet ε μhat SigmaHat}

end WassersteinDRO.Guarantees
