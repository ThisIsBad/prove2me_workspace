import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The nominal risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
implicit throughout Section 1: `R(Q,ℓ) = E_Q[ℓ(ξ)]`. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def nominalRisk {m : ℕ} (Q : Measure (EuclideanSpace ℝ (Fin m)))
    (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  ∫ x, ℓ x ∂Q

end WassersteinDRO.Guarantees
