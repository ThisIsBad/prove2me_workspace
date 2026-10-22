import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- Corollary 3.5, p. 485 (d.c. duality transportation of a local minimizer): let `x*` be a
local minimizer of `g − h` with neighbourhood `U` (`g(x) − h(x) ≥ g(x*) − h(x*)` for all
`x ∈ U ∩ dom g`), and let `y* ∈ ∂h(x*)`. If `y* ∈ int (dom g*)` and `∂g*(y*) ⊂ U` (12), then
`y*` is a local minimizer of `h* − g*`. The neighbourhood `U` is taken open, as the proof's
upper-semicontinuity step requires. -/
theorem corollary_3_5 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hfin : xs ∈ TaoAnDCA.GlobalOpt.effDom g)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hxU : xs ∈ U)
    (hmin : ∀ x ∈ U, x ∈ TaoAnDCA.GlobalOpt.effDom g → TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x)
    (hy : ys ∈ TaoAnDCA.GlobalOpt.subdiff h xs)
    (h12a : ys ∈ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)))
    (h12b : TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ⊆ U) :
    IsDCLocalMin (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys := by sorry

end TaoAnDCA.LocalOpt

