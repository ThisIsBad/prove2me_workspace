import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem lemma5_a {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) (hJ : J.Nonempty) (d : TsengCGD.Global.Vec n)
    (hd : TsengCGD.Global.IsDir f D P c H x J d) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (DJ : Set (TsengCGD.Global.Vec n)) (PJ : TsengCGD.Global.Vec n → ℝ) (DJC : Set (TsengCGD.Global.Vec n)) (PJC : TsengCGD.Global.Vec n → ℝ)
    (hw : TsengCGD.Global.IsBlockSepWitness D P J DJ PJ DJC PJC)
    (xbar : TsengCGD.Global.Vec n) (hxbar : xbar ∈ DJ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ J, (gradient f x j + (H *ᵥ WithLp.ofLp d) j) * ((x + α • d) j - xbar j))
        + c * PJ (x + α • d) - c * PJ xbar
      ≤ (α - 1) * ((1 - γ) * TsengCGD.Global.qf H d + TsengCGD.Global.Delta f P c γ H x d) := by sorry

end TsengCGD.Linear

