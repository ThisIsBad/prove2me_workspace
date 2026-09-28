import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_gelbrichHull
import Definitions.Def_WassersteinDRO_Guarantees_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The Gelbrich risk `R_ε(µ̂,Ŝ,ℓ)`, Kuhn et al. 2019, eq. (18), p. 18. Redefined locally in
this chapter's own namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. Valued
in `EReal` and guarded by `Integrable ℓ Q`. -/
noncomputable def gelbrichRisk {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : EReal :=
  ⨆ (Q : Measure (EuclideanSpace ℝ (Fin m))) (_ : Q ∈ gelbrichHull ε Ξ μhat SigmaHat)
    (_ : Integrable ℓ Q), (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Guarantees
