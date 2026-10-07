import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem lemma_2_p4 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ) :
    Z M q = ∅ ↔ ∃ u : ι → ℝ, 0 ≤ u ∧ Mᵀ *ᵥ u ≤ 0 ∧ 0 < u ⬝ᵥ q := by sorry

end LemkeLCP.Existence

