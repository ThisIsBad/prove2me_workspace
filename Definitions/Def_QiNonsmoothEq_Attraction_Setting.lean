import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Local_Setting

namespace QiNonsmoothEq.Attraction

open Filter Topology NonsmoothNewton.Local

/-- BD-regularity at `x`, Qi 1993, p. 232: `F` is directionally differentiable at `x` and
`F'(x; h) ≠ 0` for every `h ≠ 0`. -/
def BDRegularAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  QiNonsmoothEq.Local.DirDiffAt F x ∧ ∀ h : E, h ≠ 0 → dirDeriv F x h ≠ 0

/-- The norm function `g(x) = ½ F(x)ᵀF(x) = ½ ‖F(x)‖²` of Qi 1993, §1, p. 227. -/
noncomputable def normFn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : E) : ℝ :=
  (1 / 2) * ‖F x‖ ^ 2

/-- The Armijo test (4.1) of Algorithm 4.1, Qi 1993, p. 236, for the trial exponent `m`:
`g(y) - g(y + β^m s d) ≥ -σ β^m s g'(y; d)`. -/
def armijoTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (s β σ : ℝ) (y d : E) (m : ℕ) : Prop :=
  normFn F y - normFn F (y + (β ^ m * s) • d) ≥ -σ * β ^ m * s * dirDeriv (normFn F) y d

/-- A run of Algorithm 4.1 (the damped Newton method), Qi 1993, p. 236: at every step `d k`
solves the generalized Newton equation (3.12) `F(x^k) + F'(x^k; d^k) = 0`, the step size is
`α_k = β^{m_k} s` with `m_k` the first nonnegative integer passing the Armijo test (4.1), and
`x^{k+1} = x^k + α_k d^k`. The parameter ranges `s > 0`, `β ∈ (0,1)`, `σ ∈ (0,1/2)` are
hypotheses of the theorems that use the run. -/
def IsDampedNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (s β σ : ℝ) (x d : ℕ → E) (α : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, HasDirDerivAt F (x k) (d k) (-F (x k)) ∧
    (∃ m : ℕ, armijoTest F s β σ (x k) (d k) m ∧
      (∀ j < m, ¬ armijoTest F s β σ (x k) (d k) j) ∧ α k = β ^ m * s) ∧
    x (k + 1) = x k + α k • d k

end QiNonsmoothEq.Attraction
