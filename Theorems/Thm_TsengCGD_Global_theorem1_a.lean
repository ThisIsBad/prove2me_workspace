import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem theorem1_a {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α αinit : ℕ → ℝ) (β σ γ lam lamBar : ℝ)
    (hrun : IsCGDRun f D P c J H x d α)
    (harm : IsArmijo f D P c β σ γ αinit H x d α)
    (hA1 : Assumption1 H lam lamBar)
    (hinit : ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ αinit k) :
    let Δ := fun k => Delta f P c γ (H k) (x k) (d k)
    Antitone (fun k => Fc f P c (x k)) ∧
    (∀ k, x k ∈ D) ∧
    (∀ k, (1 - γ) * qf (H k) (d k) ≤ -Δ k ∧
      (1 - γ) * lam * ‖d k‖ ^ 2 ≤ (1 - γ) * qf (H k) (d k)) ∧
    (∀ k, Fc f P c (x (k + 1)) - Fc f P c (x k) ≤ σ * α k * Δ k ∧
      σ * α k * Δ k ≤ 0) := by sorry

end TsengCGD.Global

