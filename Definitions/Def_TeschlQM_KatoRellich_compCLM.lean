import Mathlib

namespace TeschlQM.KatoRellich

/-- The product `B R` of an operator `B : 𝔇(B) → ℌ` with an everywhere defined bounded operator
`R ∈ L(ℌ)`, in the usual sense of unbounded operators: `𝔇(BR) = {φ ∈ ℌ | Rφ ∈ 𝔇(B)}` and
`(BR)φ = B(Rφ)`. With `R = R_A(z)` this is Teschl's `BR_A(z)` (p. 134). -/
noncomputable def compCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := B.domain.comap (R : H →ₗ[ℂ] H)
  toFun := B.toFun.comp ((R : H →ₗ[ℂ] H).restrict (fun _ hx => hx))

end TeschlQM.KatoRellich
