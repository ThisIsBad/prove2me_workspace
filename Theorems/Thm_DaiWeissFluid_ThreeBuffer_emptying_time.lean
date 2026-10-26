import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Proof of Theorem 3.1, p. 121: under (3.1), every work-conserving fluid solution of the
three-buffer line with `|Q(0)| = 1` is empty from time `max{ρ₁/(1-ρ₁), ρ₂/(1-ρ₂)}` on, where
`ρ₁ = m₁ + m₃` and `ρ₂ = m₂` (0-based: `m 0 + m 2` and `m 1`). -/
theorem emptying_time (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T)
    (hQ0 : ∑ k, Q 0 k = 1) (t : ℝ)
    (ht : max ((m 0 + m 2) / (1 - (m 0 + m 2))) (m 1 / (1 - m 1)) ≤ t) (k : Fin 3) :
    Q t k = 0 := by sorry

end DaiWeissFluid.ThreeBuffer

