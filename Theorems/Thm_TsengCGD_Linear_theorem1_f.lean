import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem theorem1_f {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → TsengCGD.Global.Vec n) (α : ℕ → ℝ) (hrun : TsengCGD.Global.IsCGDRun f D P c J H x d α)
    (lam lamBar : ℝ) (hA1 : TsengCGD.Global.Assumption1 H lam lamBar)
    (β σ γ : ℝ) (αinit : ℕ → ℝ) (harm : TsengCGD.Global.IsArmijo f D P c β σ γ αinit H x d α)
    (hinit : ∃ a > 0, ∀ k, a ≤ αinit k)
    (L : ℝ) (hL : GradLipOn f D L) :
    (∃ a > 0, ∀ k, a ≤ α k) ∧
      (BddBelow (Set.range fun k => TsengCGD.Global.Fc f P c (x k)) →
        Tendsto (fun k => TsengCGD.Global.Delta f P c γ (H k) (x k) (d k)) atTop (𝓝 0) ∧
          Tendsto d atTop (𝓝 0)) := by sorry

end TsengCGD.Linear

