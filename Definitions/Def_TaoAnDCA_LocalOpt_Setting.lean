import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- `𝒫_l = {x* : ∂h(x*) ⊂ ∂g(x*)}` (p. 483). -/
def Pl {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | TaoAnDCA.GlobalOpt.subdiff h x ⊆ TaoAnDCA.GlobalOpt.subdiff g x}

/-- `𝒟_l = {y* : ∂g*(y*) ⊂ ∂h*(y*)}` (p. 483). -/
def Dl {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y ⊆ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj h) y}

/-- `x*` is a critical point of `g − h`: `∂g(x*) ∩ ∂h(x*) ≠ ∅` (p. 482). -/
def IsCritical {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (TaoAnDCA.GlobalOpt.subdiff g x ∩ TaoAnDCA.GlobalOpt.subdiff h x).Nonempty

/-- `x*` is a local minimizer of `g − h` (4) (p. 482): `(g − h)(x*)` is finite and
`(g − h)(x*) ≤ (g − h)(x)` on a neighbourhood of `x*`. -/
def IsDCLocalMin {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊤ ∧ TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊥ ∧ ∃ U ∈ 𝓝 x, ∀ z ∈ U, TaoAnDCA.GlobalOpt.dcSub g h x ≤ TaoAnDCA.GlobalOpt.dcSub g h z

/-- `x*` is a strict local minimizer of `g − h` (Corollary 3.4, p. 485): `(g − h)(x*)` is finite
and `(g − h)(x*) < (g − h)(x)` for every `x ≠ x*` in a neighbourhood of `x*` ((4) with strict
inequality off `x*`). -/
def IsDCStrictLocalMin {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊤ ∧ TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊥ ∧ ∃ U ∈ 𝓝 x, ∀ z ∈ U, z ≠ x → TaoAnDCA.GlobalOpt.dcSub g h x < TaoAnDCA.GlobalOpt.dcSub g h z

end TaoAnDCA.LocalOpt
