import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem part_ii (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ)
    (F : Finset (Sym2 (GV φ))) (hF : IsEdgeDominating (G φ) F)
    (hcard : F.card = 3 * numVars φ) :
    CookLevin.Satisfies (assignOfEdges φ F) φ := by sorry

end EdgeDomSets.NPC

