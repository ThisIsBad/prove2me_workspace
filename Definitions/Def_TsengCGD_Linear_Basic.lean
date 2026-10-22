import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Linear

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- X̄, the set of stationary points of F_c (p. 404). -/
def statSet (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) : Set (TsengCGD.Global.Vec n) :=
  {x | TsengCGD.Global.IsStationary f D P c x}

/-- The restricted Gauss–Seidel rule (12): 𝒯 = {t 0 < t 1 < ⋯} with t 0 = 0, τ(t i) = t (i+1),
and 𝒥^{t i}, …, 𝒥^{t(i+1)−1} pairwise disjoint with union 𝒩. -/
def RestrictedGaussSeidel (J : ℕ → Finset (Fin n)) (t : ℕ → ℕ) : Prop :=
  StrictMono t ∧ t 0 = 0 ∧ ∀ i,
    ((Finset.Ico (t i) (t (i + 1)) : Set ℕ).PairwiseDisjoint J) ∧
      (Finset.Ico (t i) (t (i + 1))).biUnion J = Finset.univ

/-- (22): ∇f is L-Lipschitz on dom P, L ≥ 0. -/
def GradLipOn (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ y ∈ D, ∀ z ∈ D, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖

/-- Assumption 2(a) (p. 404). -/
def Assumption2a (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) : Prop :=
  (statSet f D P c).Nonempty ∧ ∀ ζ : ℝ, ∃ τ > 0, ∃ ε > 0, ∀ x ∈ D,
    TsengCGD.Global.Fc f P c x ≤ ζ → ‖TsengCGD.Global.dI f D P c x‖ ≤ ε →
      Metric.infDist x (statSet f D P c) ≤ τ * ‖TsengCGD.Global.dI f D P c x‖

/-- Assumption 2(b) (p. 404). -/
def Assumption2b (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) : Prop :=
  ∃ δ > 0, ∀ x ∈ statSet f D P c, ∀ y ∈ statSet f D P c, TsengCGD.Global.Fc f P c x ≠ TsengCGD.Global.Fc f P c y → δ ≤ ‖x - y‖

/-- At least Q-linear convergence of a real sequence ([42, Chap. 9]): it converges to some v and
eventually |s_{i+1} − v| ≤ q|s_i − v| for a q < 1. -/
def QLinear (s : ℕ → ℝ) : Prop :=
  ∃ v, Tendsto s atTop (𝓝 v) ∧ ∃ q, 0 ≤ q ∧ q < 1 ∧ ∀ᶠ i in atTop, |s (i + 1) - v| ≤ q * |s i - v|

/-- At least R-linear convergence of a vector sequence: ‖s_i − x̄‖ ≤ C qⁱ for a limit x̄ and q < 1
(equivalently lim sup ‖s_i − x̄‖^{1/i} < 1, footnote 2 p. 409). -/
def RLinear (s : ℕ → TsengCGD.Global.Vec n) : Prop :=
  ∃ xbar : TsengCGD.Global.Vec n, ∃ C q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i, ‖s i - xbar‖ ≤ C * q ^ i

/-- ‖d‖_p = (Σ_j |d_j|^p)^{1/p} (p. 390), real p ≥ 1. -/
noncomputable def pNorm (p : ℝ) (d : TsengCGD.Global.Vec n) : ℝ := (∑ j, |d j| ^ p) ^ (1 / p)

/-- ‖g_𝒥‖_q, the q-norm of the subvector indexed by 𝒥. -/
noncomputable def pNormOn (p : ℝ) (J : Finset (Fin n)) (g : TsengCGD.Global.Vec n) : ℝ :=
  (∑ j ∈ J, |g j| ^ p) ^ (1 / p)

/-- r^k = Σ_{ℓ=k}^{τ(k)−1} ‖d^ℓ‖ of Theorem 2(a), for k = t i ∈ 𝒯 and τ(k) = t (i+1). -/
noncomputable def r (t : ℕ → ℕ) (d : ℕ → TsengCGD.Global.Vec n) (i : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Ico (t i) (t (i + 1)), ‖d ℓ‖

end TsengCGD.Linear
