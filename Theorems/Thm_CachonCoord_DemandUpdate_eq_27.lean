import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, Eq. (27), p. 66. Let `q2sel` select a supply chain optimal
period-2 order `q_2(q_1, ξ)`. At every `q_1 > 0` for which (26) has a solution `ξ(q_1) = xi1 ≥ 0`,
`Ω_1` is differentiable with
`∂Ω_1(q_1)/∂q_1 = −c_1 + c_2(1 − G(ξ(q_1))) + ∫_0^{ξ(q_1)} pS'(q_1|ξ) g(ξ) dξ`, where
`S'(q|ξ) = 1 − F(q|ξ)`; and at a supply chain optimal `q_1° > 0` this derivative is `0`. -/
theorem eq_27 (M : Model) (q2sel : ℝ → ℝ → ℝ) (hq2 : M.IsChainPeriod2Optimal q2sel) :
    (∀ q1 xi1, 0 < q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio →
      HasDerivAt (M.Omega1 q2sel)
        (-M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1) * M.g ξ) q1) ∧
    (∀ q1o xi1, 0 < q1o → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1o →
      0 ≤ xi1 → M.F xi1 q1o = M.ratio →
      -M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1o) * M.g ξ = 0) := by sorry

end CachonCoord.DemandUpdate

