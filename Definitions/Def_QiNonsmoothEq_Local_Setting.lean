import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
open Filter Topology

namespace QiNonsmoothEq.Local

/-- Qi (1993), §2, p. 229: `F` is directionally differentiable at `x`, i.e. the one-sided
directional derivative `F'(x; h)` exists for every direction `h`. -/
def DirDiffAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  ∀ h : E, ∃ d : G, NonsmoothNewton.Local.HasDirDerivAt F x h d

/-- Qi (1993), (2.1), p. 229: `F` is B-differentiable at `x` if it is directionally
differentiable at `x` and `(F(x + h) - F(x) - F'(x; h)) / ‖h‖ → 0` as `h → 0`. -/
def BDiffAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  DirDiffAt F x ∧
    Tendsto (fun h : E => ‖h‖⁻¹ * ‖F (x + h) - F x - NonsmoothNewton.Local.dirDeriv F x h‖)
      (𝓝[≠] 0) (𝓝 0)

/-- Qi (1993), (2.4), p. 229: the directional derivative `F'(·, ·)` is semicontinuous at `x`:
for every `ε > 0` there is a neighbourhood `N` of `x` with
`‖F'(x + h; h) - F'(x; h)‖ ≤ ε ‖h‖` whenever `x + h ∈ N`. The page defines it only when `F` is
B-differentiable on a neighbourhood of `x`; every statement using it assumes that. -/
def SemicontAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  ∀ ε > 0, ∃ N ∈ 𝓝 x, ∀ h : E, x + h ∈ N →
    ‖NonsmoothNewton.Local.dirDeriv F (x + h) h - NonsmoothNewton.Local.dirDeriv F x h‖ ≤ ε * ‖h‖

/-- Qi (1993), (2.5), p. 229: `F'(·, ·)` is semicontinuous of degree 2 at `x`: there are a
constant `L` and a neighbourhood `N` of `x` with `‖F'(x + h; h) - F'(x; h)‖ ≤ L ‖h‖²` whenever
`x + h ∈ N`. Used only under B-differentiability on a neighbourhood of `x`. -/
def SemicontDeg2At {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  ∃ L : ℝ, ∃ N ∈ 𝓝 x, ∀ h : E, x + h ∈ N →
    ‖NonsmoothNewton.Local.dirDeriv F (x + h) h - NonsmoothNewton.Local.dirDeriv F x h‖ ≤
      L * ‖h‖ ^ 2

/-- `W` is a two-sided inverse of the linear map `V`; "`V` nonsingular with `‖V⁻¹‖ ≤ c`" is
written `∃ W, IsInverse V W ∧ ‖W‖ ≤ c`. -/
def IsInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V W : E →L[ℝ] E) : Prop :=
  W.comp V = ContinuousLinearMap.id ℝ E ∧ V.comp W = ContinuousLinearMap.id ℝ E

/-- Qi (1993), p. 233: `F` is strongly BD-regular at `x` if every `V ∈ ∂_B F(x)` is
nonsingular. -/
def StronglyBDRegularAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : E) : Prop :=
  ∀ V ∈ NonsmoothNewton.Shared.bJac F x, ∃ W : E →L[ℝ] E, IsInverse V W

/-- A run of the generalized-Jacobian Newton method (3.2), Qi (1993), p. 234:
`x^{k+1} = x^k - V_k⁻¹ F(x^k)` with `V_k ∈ ∂_B F(x^k)`, written without an inverse as
`V_k (x^{k+1} - x^k) = -F(x^k)`. Every choice of `V_k ∈ ∂_B F(x^k)` is allowed. -/
def IsBDNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : ℕ → E) (V : ℕ → E →L[ℝ] E) : Prop :=
  ∀ k, V k ∈ NonsmoothNewton.Shared.bJac F (x k) ∧ V k (x (k + 1) - x k) = -F (x k)

/-- A run of the directional-derivative-based Newton method (3.11)–(3.12), Qi (1993), p. 235:
`x^{k+1} = x^k + d^k` with `F(x^k) + F'(x^k; d^k) = 0`, i.e. `F'(x^k; x^{k+1} - x^k)` exists and
equals `-F(x^k)`. -/
def IsDirNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : ℕ → E) : Prop :=
  ∀ k, NonsmoothNewton.Local.HasDirDerivAt F (x k) (x (k + 1) - x k) (-F (x k))

/-- Final Remark (6), Qi (1993), p. 243: `G : ℝ² → ℝ²`, `G(u, v) = (-u, u² - v)`. -/
noncomputable def remarkG (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-(x 0), (x 0) ^ 2 - x 1]

/-- Final Remark (6), Qi (1993), p. 243: `x₊ = (u₊, v₊)` with `a₊ = max(a, 0)`. -/
noncomputable def posPartVec (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[max (x 0) 0, max (x 1) 0]

/-- Final Remark (6), Qi (1993), p. 244: `F(x) = G(x₊) + x - x₊`. -/
noncomputable def remarkF (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  remarkG (posPartVec x) + x - posPartVec x

end QiNonsmoothEq.Local
