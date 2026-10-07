import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem theorem_4_ray_step {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (q : ι → ℝ) (hM : CopositivePlus M)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    (zb0 = 0 ∧ IsEquilibriumPoint M q zb) ∨ (0 < zb0 ∧ Z M q = ∅) := by sorry

end LemkeLCP.Existence

