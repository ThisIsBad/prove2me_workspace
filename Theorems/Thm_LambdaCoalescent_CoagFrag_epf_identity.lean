import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

theorem epf_identity (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ) (n : ℕ) (π₁ π₂ : Setoid (Fin n)) (h : π₁ ≤ π₂) :
    pdEPF α θ (blockSizes π₁) * pdEPF β (θ / α) (coagCounts π₁ π₂) =
      ((fragSizes π₁ π₂).map (pdEPF α (-(α * β)))).prod * pdEPF (α * β) θ (blockSizes π₂) := by sorry

end LambdaCoalescent.CoagFrag

