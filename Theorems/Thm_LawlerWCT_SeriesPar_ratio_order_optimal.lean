import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.SeriesPar

theorem ratio_order_optimal {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (F : List (List ι)) (hne : ∀ c ∈ F, c ≠ []) (hnd : F.flatten.Nodup)
    (hp : ∀ j ∈ F.flatten, 0 < p j) :
    ∀ L L' : List (List ι), L.Perm F → IsRatioOrder p w L → L'.Perm F →
      SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L.flatten ≤
        SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L'.flatten := by sorry

end LawlerWCT.SeriesPar

