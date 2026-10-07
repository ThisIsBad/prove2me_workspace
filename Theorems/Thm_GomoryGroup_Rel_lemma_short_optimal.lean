import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem lemma_short_optimal {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0) :
    ∃ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1 := by sorry

end GomoryGroup.Rel

