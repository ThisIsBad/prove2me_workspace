import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem theorem1_e {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k)
    (hGS : GaussSeidel J) (hsep : ∀ k, BlockSeparable D P (J k))
    (hsup : ∃ A : ℝ, ∀ k, α k ≤ A) :
    ∀ xbar : Vec n, MapClusterPt xbar atTop x → IsStationary f D P c xbar := by sorry

end TsengCGD.Global

