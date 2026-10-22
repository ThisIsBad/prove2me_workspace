import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem theorem_4_3 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (hB : ∀ y, BDiffAt F y)
    (β σ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hrun : IsDampedNewtonRun F 1 β σ x d α) (hne : ∀ k, F (x k) ≠ 0)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hclu : MapClusterPt xstar atTop x) (hzero : F xstar = 0)
    (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    Tendsto x atTop (𝓝 xstar) ∧
      (fun k => x (k + 1) - xstar) =o[atTop] (fun k => x k - xstar) ∧
      ∀ᶠ k in atTop, α k = 1 := by sorry

end QiNonsmoothEq.Damped

