import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- Theorem 3.2 (ii), p. 484: let `x*` be a critical point of `g − h` and
`y* ∈ ∂g(x*) ∩ ∂h(x*)`, and let `U` be a neighbourhood of `x*` with `U ∩ dom g ⊂ dom ∂h`.
If for every `x ∈ U ∩ dom g` there is `y ∈ ∂h(x)` with `h*(y) − g*(y) ≥ h*(y*) − g*(y*)`,
then `x*` is a local minimizer of `g − h`; more precisely
`g(x) − h(x) ≥ g(x*) − h(x*)` for all `x ∈ U ∩ dom g`. -/
theorem theorem_3_2_ii {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hys : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ 𝓝 xs)
    (hdom : U ∩ TaoAnDCA.GlobalOpt.effDom g ⊆ {x | (TaoAnDCA.GlobalOpt.subdiff h x).Nonempty})
    (hcond : ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, ∃ y ∈ TaoAnDCA.GlobalOpt.subdiff h x,
      TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ≤
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) :
    IsDCLocalMin g h xs ∧ ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x := by sorry

end TaoAnDCA.LocalOpt

