import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 272): on an input of `EC(k)` with `T ≠ ∅` and `a = F*/|T|`, every
halting run of C2 has cumulative overlap `OV(F₁) ≤ |T|(a[ln(k) + 1] − 1)`. -/
theorem overlap_le {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (F : Input α)
    (hF : InEC k F) (hT : F.ground.Nonempty) {σ : State F} {ov : ℕ}
    (hrun : RunOV F σ ov) (hσ : Halts σ) :
    (ov : ℝ) ≤ (F.ground.card : ℝ) *
      (((F.opt : ℝ) / (F.ground.card : ℝ)) * (Real.log k + 1) - 1) := by sorry

end JohnsonApprox.ExactCover

