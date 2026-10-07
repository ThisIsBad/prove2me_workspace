import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem subtree_isModule {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N) (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (T : SPTree ι) (hT : T.leaves.Nodup) (hTN : ∀ j, j ∈ T.leaves ↔ j ∈ N)
    (hTG : ∀ i ∈ N, ∀ j ∈ N, Relation.TransGen G i j ↔ T.prec i j)
    (S : SPTree ι) (hS : S.IsSubtree T) :
    IsModule G N S.leaves.toFinset := by sorry

end LawlerWCT.SeriesPar

