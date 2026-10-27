import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

namespace EdgeDomSets.NPC

theorem G_degree (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ) :
    MaxDegreeLE (G φ) 4 ∧
      ∀ w : GV φ, ¬ DegreeLE (G φ) w 3 ↔
        ∃ j : Fin φ.length, (φ.get j).length = 3 ∧
          ((w = dNode j ∧ ∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Pos v) ∨
            (w = dNode' j ∧ ∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Neg v)) := by sorry

end EdgeDomSets.NPC

