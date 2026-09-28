import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 271): if C2 may choose `S′` with `Ratio(S′) ≥ y`, then
`|UNCOV| ≤ F*/(y + 1)` (stated multiplicatively). -/
theorem uncov_card_bound_of_ratio_ge {α : Type} [DecidableEq α] (F : Input α)
    {σ : State F} {i : Fin F.p} (hσ : Reachable F σ) (hi : MayChoose F σ i) (y : ℝ)
    (hy : y * ((F.S i ∩ σ.UNCOV).card : ℝ) ≤ ((F.S i \ σ.UNCOV).card : ℝ)) :
    (y + 1) * (σ.UNCOV.card : ℝ) ≤ (F.opt : ℝ) := by sorry

end JohnsonApprox.ExactCover

