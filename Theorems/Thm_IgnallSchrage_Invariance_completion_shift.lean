import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2

namespace IgnallSchrage.Invariance

/-- p. 411: adding a constant `G` to all processing times (all nonnegative) raises the completion time of the
`r`-th job of a permutation schedule on machine `M` by `G (r + M - 1)`. Three machines: after
`r ≥ 1` positions, machines A, B, C finish `r G`, `(r + 1) G`, `(r + 2) G` later; two machines:
machine B finishes `(r + 1) G` later. -/
theorem completion_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    JohnsonFlowShop.ThreeStage.asapDone (fun i => a i + G) (fun i => b i + G)
        (fun i => c i + G) σ r =
      ((JohnsonFlowShop.ThreeStage.asapDone a b c σ r).1 + r * G,
       (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.1 + (r + 1) * G,
       (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.2 + (r + 2) * G) ∧
    JohnsonFlowShop.TwoStage.asapC2 (fun i => a i + G) (fun i => b i + G) σ r =
      JohnsonFlowShop.TwoStage.asapC2 a b σ r + (r + 1) * G := by sorry

end IgnallSchrage.Invariance

