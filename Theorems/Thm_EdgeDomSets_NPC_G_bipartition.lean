import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem G_bipartition (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ) :
    (∀ a b : GV φ, (G φ).Adj a b → inS a ≠ inS b) ∧ (G φ).Colorable 2 := by sorry

end EdgeDomSets.NPC

