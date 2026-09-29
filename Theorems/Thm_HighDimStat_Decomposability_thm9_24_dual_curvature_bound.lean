import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Theorem 9.24 (p. 285): given a target `θ* ∈ M`, under (A1') — the cost satisfies the
`Φ*`-curvature condition with curvature `κ`, tolerance `τn` and radius `R`, witnessed by the
gradient-increment map `Dg : Δ ↦ ∇Ln(θ*+Δ) - ∇Ln(θ*)` — and (A2) — `Φ` decomposable with
respect to `(M, M̄)` — suppose `τn Ψ(M̄)² < κ/32`. Conditioned on `G(λn) ∩ {Φ*(θ̂-θ*) ≤ R}`, any
optimal solution `θ̂` of the M-estimator satisfies `Φ*(θ̂ - θ*) ≤ 3λn/κ`. -/
theorem thm9_24_dual_curvature_bound
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (Dg : Ω → Ω)
    (lamN κ τn R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hθM : θstar ∈ M)
    (hgrad : HasGradientAt Ln g θstar)
    (hDg : ∀ Δ : Ω, HasGradientAt Ln (g + Dg Δ) (θstar + Δ))
    (hcurv : DualCurvature Dg Φ κ τn R)
    (hκ : 0 < κ) (hlam : 0 < lamN)
    (htol : τn * subspaceLip Φ Mbar ^ 2 < κ / 32)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (hR : dualNorm Φ (θhat - θstar) ≤ R) :
    dualNorm Φ (θhat - θstar) ≤ 3 * lamN / κ := by sorry

end HighDimStat.Decomposability
