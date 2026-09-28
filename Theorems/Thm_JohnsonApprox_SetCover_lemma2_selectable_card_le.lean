import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_Config

namespace JohnsonApprox.SetCover

theorem lemma2_selectable_card_le {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (K : Config ι α) (M1 M0 : Finset ι)
    (h1 : Selectable K M1) (h0 : M0.biUnion K.SET = K.UNCOV) :
    (M1.card : ℚ) ≤ ∑ i ∈ M0, harmonic (K.SET i).card := by sorry

end JohnsonApprox.SetCover

