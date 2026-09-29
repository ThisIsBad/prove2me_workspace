import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Proposition 9.13 (p. 273, "a key consequence of decomposability"): let `Ln` be convex with
score `g = ∇Ln(θ*)`, `Φ` a norm decomposable with respect to `(M, M̄)`, and `θ̂` any optimal
solution of the regularized M-estimator `min_θ Ln(θ) + λn Φ(θ)`. Conditioned on the good event
`G(λn) = {Φ*(g) ≤ λn/2}`, the error `Δ = θ̂ - θ*` lies in the cone `C_{θ*}(M, M̄)`. -/
theorem prop9_13_basic_inequality
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN) :
    θhat - θstar ∈ errorCone Φ M Mbar θstar := by sorry

end HighDimStat.Decomposability
