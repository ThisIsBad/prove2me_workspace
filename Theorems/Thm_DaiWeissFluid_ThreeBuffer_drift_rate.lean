import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Proof of Theorem 3.1, p. 121: under (3.1), along every work-conserving fluid solution of the
three-buffer line, at a time `t > 0` where station `i` (0-based) has positive volume and `G_i` is
differentiable, `Ġ_i(t) = -(1/ρ_i - 1) < 0`. -/
theorem drift_rate (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T) (i : Fin 2) (t : ℝ)
    (ht : 0 < t) (hW : 0 < (threeBuffer m).volume Q i t) (d : ℝ)
    (hd : HasDerivAt (lyap m Q i) d t) :
    d = -(1 / (threeBuffer m).ρ i - 1) ∧ d < 0 := by sorry

end DaiWeissFluid.ThreeBuffer

