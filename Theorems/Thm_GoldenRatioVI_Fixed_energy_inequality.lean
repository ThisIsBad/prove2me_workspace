import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio

namespace GoldenRatioVI.Fixed

/-- Eq. (14), the energy inequality of the fixed-step Golden Ratio Algorithm: under (C2), (C3),
`F` `L`-Lipschitz on `dom g`, `λ ∈ (0, φ/(2L)]`, for a run of (6) with `z¹ ∈ dom g`, every
solution `z* ∈ S` and every `k ≥ 2`,
`(1+φ)‖z̄ᵏ⁺¹ - z*‖² + (φ/2)‖zᵏ⁺¹ - zᵏ‖²
   ≤ (1+φ)‖z̄ᵏ - z*‖² + (φ/2)‖zᵏ - zᵏ⁻¹‖² - φ‖zᵏ - z̄ᵏ‖²`. -/
theorem energy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → EReal) (F : E → E) (L lam : ℝ) (z zbar : ℕ → E)
    (hg : IsProperConvexLSC g) (hF : IsMonotoneOperatorOn F (effDom g))
    (hL : 0 < L) (hLip : ∀ u ∈ effDom g, ∀ v ∈ effDom g, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (hlam : 0 < lam) (hlamL : lam ≤ φ / (2 * L))
    (hrun : IsGRAALRun g F lam z zbar) (hz1 : z 1 ∈ effDom g)
    (zs : E) (hzs : zs ∈ solutionSet g F) (k : ℕ) (hk : 2 ≤ k) :
    (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 + φ / 2 * ‖z (k + 1) - z k‖ ^ 2 ≤
      (1 + φ) * ‖zbar k - zs‖ ^ 2 + φ / 2 * ‖z k - z (k - 1)‖ ^ 2
        - φ * ‖z k - zbar k‖ ^ 2 := by sorry

end GoldenRatioVI.Fixed

