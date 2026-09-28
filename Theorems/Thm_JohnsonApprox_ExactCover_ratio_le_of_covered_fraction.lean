import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 271): with `a = F*/|T|` and `x = |T − UNCOV|/|T|`, the next set `S′`
chosen by C2 has `Ratio(S′) ≤ a/(1 − x) − 1`. -/
theorem ratio_le_of_covered_fraction {α : Type} [DecidableEq α] (F : Input α)
    (hT : F.ground.Nonempty) {σ : State F} {i : Fin F.p} (hσ : Reachable F σ)
    (hi : MayChoose F σ i) :
    ((F.S i \ σ.UNCOV).card : ℝ) / ((F.S i ∩ σ.UNCOV).card : ℝ) ≤
      ((F.opt : ℝ) / (F.ground.card : ℝ)) /
        (1 - ((F.ground \ σ.UNCOV).card : ℝ) / (F.ground.card : ℝ)) - 1 := by sorry

end JohnsonApprox.ExactCover

