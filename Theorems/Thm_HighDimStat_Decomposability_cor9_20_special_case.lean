import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

/-- Corollary 9.20 (p. 281): in addition to the conditions of Theorem 9.19, suppose the target
`θ*` belongs to the model subspace `M`. Then any optimal solution `θ̂` of the M-estimator
satisfies both `Φ(θ̂ - θ*) ≤ 6λn/κ · Ψ(M̄)²` and `‖θ̂ - θ*‖² ≤ 9λn²/κ² · Ψ(M̄)²`. -/
theorem cor9_20_special_case
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R)
    (hθM : θstar ∈ M) :
    Φ (θhat - θstar) ≤ 6 * lamN / κ * subspaceLip Φ Mbar ^ 2 ∧
      ‖θhat - θstar‖ ^ 2 ≤ 9 * lamN ^ 2 / κ ^ 2 * subspaceLip Φ Mbar ^ 2 := by sorry

end HighDimStat.Decomposability
