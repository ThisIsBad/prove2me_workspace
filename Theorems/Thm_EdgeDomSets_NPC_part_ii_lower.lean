import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem part_ii_lower (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ)
    (F : Finset (Sym2 (GV φ))) (hF : IsEdgeDominating (G φ) F) :
    (∀ o : Occ φ, ∃ f ∈ F, lit o ∈ f) ∧ 3 * numVars φ ≤ F.card := by sorry

end EdgeDomSets.NPC

