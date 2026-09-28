import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 271): for a run of C2 that halts, `m(F₁) = |T| + OV(F₁)`. -/
theorem measure_eq_card_add_overlap {α : Type} [DecidableEq α] (F : Input α)
    {σ : State F} {ov : ℕ} (hrun : RunOV F σ ov) (hσ : Halts σ) :
    F.measure σ.SUB = F.ground.card + ov := by sorry

end JohnsonApprox.ExactCover

