import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem lemma5_b {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (hJ : J.Nonempty) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (L : ℝ) (hL : GradLipOn f D L) (lam : ℝ) (hlam : 0 < lam)
    (hHlam : ∀ z : TsengCGD.Global.Vec n, lam * ‖z‖ ^ 2 ≤ TsengCGD.Global.qf H z)
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hαL : α * L ≤ 2 * lam * (1 - σ + σ * γ)) :
    x + α • d ∈ D ∧ TsengCGD.Global.Fc f P c (x + α • d) - TsengCGD.Global.Fc f P c x ≤ σ * α * TsengCGD.Global.Delta f P c γ H x d := by sorry

end TsengCGD.Linear

