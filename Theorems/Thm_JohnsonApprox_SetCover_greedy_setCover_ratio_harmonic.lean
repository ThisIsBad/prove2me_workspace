import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1

namespace JohnsonApprox.SetCover

theorem greedy_setCover_ratio_harmonic (k : ℕ) (hk : 1 ≤ k) :
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InSC k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → (F₁.card : ℚ) ≤ harmonic k * opt S) ∧
      (∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α), InSC k S ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          (F₁.card : ℚ) = harmonic k * opt S) := by sorry

end JohnsonApprox.SetCover

