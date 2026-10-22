import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_NonsmoothNewton_Local_dirDeriv

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

/-- `F` is directionally differentiable at `x`: the one-sided directional derivative
`F'(x; h)` exists for every direction `h` (Qi 1993, §2, p. 229). -/
def DirDiffAt {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ h, ∃ d, HasDirDerivAt F x h d

/-- B-differentiability at `x`, Qi 1993, (2.1), p. 229: `F` is directionally differentiable
at `x` and `(F(x + h) - F(x) - F'(x; h)) / ‖h‖ → 0` as `h → 0`. -/
def BDiffAt {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  DirDiffAt F x ∧
    Tendsto (fun h => ‖h‖⁻¹ * ‖F (x + h) - F x - dirDeriv F x h‖) (𝓝[≠] 0) (𝓝 0)

/-- The directional derivative `F'(·, ·)` is semicontinuous of degree 2 at `x`,
Qi 1993, (2.5), p. 229: there are a constant `L` and a neighbourhood `N` of `x` with
`‖F'(x + h; h) - F'(x; h)‖ ≤ L ‖h‖²` whenever `x + h ∈ N`. (Every statement using it also
assumes directional differentiability on a neighbourhood of `x`, as the page does.) -/
def SemicontDeg2At {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ L : ℝ, ∃ N ∈ 𝓝 x, ∀ h, x + h ∈ N →
    ‖dirDeriv F (x + h) h - dirDeriv F x h‖ ≤ L * ‖h‖ ^ 2

/-- `W` is a two-sided inverse of the linear operator `V`. "`V` is nonsingular" is
`∃ W, IsInverse V W`. -/
def IsInverse {n : ℕ} (V W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  W.comp V = ContinuousLinearMap.id ℝ _ ∧ V.comp W = ContinuousLinearMap.id ℝ _

/-- Strong BD-regularity, Qi 1993, p. 233: every `V ∈ ∂_B F(x)` is nonsingular. -/
def StronglyBDRegularAt {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ V ∈ bJac F x, ∃ W, IsInverse V W

/-- The norm function `g(x) = ½ F(x)ᵀF(x) = ½ ‖F(x)‖²` of Qi 1993, §1, p. 227. -/
noncomputable def normFn {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * ‖F x‖ ^ 2

/-- The Armijo test (4.1) of Algorithm 4.1, Qi 1993, p. 236, at the trial index `m`:
`g(y) - g(y + β^m s d) ≥ -σ β^m s g'(y; d)`. -/
def armijoTest {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s β σ : ℝ) (y d : EuclideanSpace ℝ (Fin n)) (m : ℕ) : Prop :=
  normFn F y - normFn F (y + (β ^ m * s) • d) ≥ -σ * β ^ m * s * dirDeriv (normFn F) y d

/-- A run of the damped Newton method, Algorithm 4.1, Qi 1993, p. 236: at every step `d k`
solves the generalized Newton equation (3.12) `F(x^k) + F'(x^k; d^k) = 0`, the step is
`α_k = β^{m_k} s` where `m_k` is the first nonnegative integer passing (4.1), and
`x^{k+1} = x^k + α_k d^k`. -/
def IsDampedNewtonRun {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s β σ : ℝ) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) : Prop :=
  ∀ k, HasDirDerivAt F (x k) (d k) (-F (x k)) ∧
    (∃ m : ℕ, armijoTest F s β σ (x k) (d k) m ∧
      (∀ j < m, ¬ armijoTest F s β σ (x k) (d k) j) ∧ α k = β ^ m * s) ∧
    x (k + 1) = x k + α k • d k

end QiNonsmoothEq.Damped
