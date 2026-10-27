import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem part_i (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ)
    (α : CookLevin.Assignment) (hα : CookLevin.Satisfies α φ) :
    IsEdgeDominating (G φ) (assignEdges φ α) ∧
      (assignEdges φ α).card = 3 * numVars φ := by sorry

end EdgeDomSets.NPC

