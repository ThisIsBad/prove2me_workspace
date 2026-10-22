import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Linear

theorem lemma4 {n : ℕ} (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c)
    (h : TsengCGD.Global.Vec n → ℝ) (hh : ContDiff ℝ 1 h) (ρ p q : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (hq : 1 / p + 1 / q = 1)
    (hmono : ∀ u v : TsengCGD.Global.Vec n, ρ * pNorm p (u - v) ^ p ≤ ⟪gradient h u - gradient h v, u - v⟫)
    (x : TsengCGD.Global.Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty) (gb gt db dt : TsengCGD.Global.Vec n)
    (hdb : TsengCGD.Global.SupportedOn J db ∧ x + db ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gb, db⟫ + h db + c * P (x + db) ≤ ⟪gb, d'⟫ + h d' + c * P (x + d'))
    (hdt : TsengCGD.Global.SupportedOn J dt ∧ x + dt ∈ D ∧ ∀ d', TsengCGD.Global.SupportedOn J d' → x + d' ∈ D →
      ⟪gt, dt⟫ + h dt + c * P (x + dt) ≤ ⟪gt, d'⟫ + h d' + c * P (x + d')) :
    pNorm p (db - dt) ≤ ρ ^ (-q / p) * pNormOn q J (gb - gt) ^ (q / p) := by sorry

end TsengCGD.Linear

