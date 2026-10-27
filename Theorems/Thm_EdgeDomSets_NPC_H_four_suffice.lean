import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem H_four_suffice (S : Finset (Fin 3)) (hS : S.Nonempty) :
    ∃ D : Finset (Sym2 (Fin 14)), EdsRestricted S D ∧ D.card = 4 := by sorry

end EdgeDomSets.NPC

