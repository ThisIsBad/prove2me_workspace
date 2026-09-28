import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SetCover_Config

namespace JohnsonApprox.SetCover

theorem lemma1_choosable_iff_selectable {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (hS : Function.Injective S)
    (F₁ : Finset (Finset α)) (hF₁ : F₁ ∈ subcovers S) :
    Choosable S F₁ ↔ Selectable (initConfig S) (Finset.univ.filter (fun i => S i ∈ F₁)) := by sorry

end JohnsonApprox.SetCover

