import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem theorem2_a {n : ℕ} (L lam lamBar : ℝ) :
    ∃ C > 0, ∀ (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
      (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (t : ℕ → ℕ),
      TsengCGD.Global.Standing f D P c → GradLipOn f D L → TsengCGD.Global.IsCGDRun f D P c J H x d α →
      (∀ k, x k ∈ D) → TsengCGD.Global.Assumption1 H lam lamBar → RestrictedGaussSeidel J t →
      (∀ k, TsengCGD.Global.BlockSeparable D P (J k)) →
      ∀ abar : ℝ, (∀ j, α j ≤ abar) →
      ∀ i, ‖TsengCGD.Global.dI f D P c (x (t i))‖ ≤ max 1 abar * C * r t d i := by sorry

end TsengCGD.Linear

