import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem theorem1_b {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (xbar : Vec n)
    (hconv : Tendsto (x ∘ φ) atTop (𝓝 xbar)) :
    let Δ := fun k => Delta f P c γ (H k) (x k) (d k)
    Tendsto (fun k => α k * Δ k) atTop (𝓝 0) ∧
    Tendsto (d ∘ φ) atTop (𝓝 0) ∧
    ∀ (Dk : ℕ → Matrix (Fin n) (Fin n) ℝ) (del delBar : ℝ),
      0 < del → del ≤ delBar →
      (∀ k, IsPosDiag (Dk k) ∧
        ∀ z : Vec n, del * ‖z‖ ^ 2 ≤ qf (Dk k) z ∧
          qf (Dk k) z ≤ delBar * ‖z‖ ^ 2) →
      Tendsto (fun i => dH f D P c (Dk (φ i)) (x (φ i)) (J (φ i)))
        atTop (𝓝 0) := by sorry

end TsengCGD.Global

