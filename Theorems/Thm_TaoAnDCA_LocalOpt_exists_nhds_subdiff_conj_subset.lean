import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- §3.2, proof of Corollary 3.5, p. 485 (upper semicontinuity of `∂g*`): if
`y* ∈ int (dom g*)` and `∂g*(y*) ⊂ U` with `U` open, then `y*` has a neighbourhood
`V ⊂ int (dom g*)` with `∂g*(V) ⊂ U`, and more precisely `∂g*(V) ⊂ U ∩ dom g`. -/
theorem exists_nhds_subdiff_conj_subset {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h) (ys : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h12a : ys ∈ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)))
    (h12b : TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ⊆ U) :
    ∃ V ∈ 𝓝 ys, V ⊆ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)) ∧
      ∀ y ∈ V, TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y ⊆ U ∩ TaoAnDCA.GlobalOpt.effDom g := by sorry

end TaoAnDCA.LocalOpt

