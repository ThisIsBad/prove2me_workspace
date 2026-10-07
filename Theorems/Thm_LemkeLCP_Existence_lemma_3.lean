import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem lemma_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    u ⬝ᵥ (M *ᵥ u) + u0 = 0 := by sorry

end LemkeLCP.Existence

