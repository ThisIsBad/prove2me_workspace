import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_FirstOrderAlgorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open MeasureTheory

namespace OnlineConvexOpt.BanditConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- Lemma 6.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
p. 108, PDF p. 130). Let `u ∈ K` be fixed and `f_1, ..., f_T : K → ℝ` differentiable (with
gradient map `gradf`). Let `A` be a first order online algorithm (Definition 6.4) that ensures,
in the full information setting, a regret bound `Regret_T(A) ≤ B(∇f_1(x_1), ..., ∇f_T(x_T))` for
every differentiable cost sequence, where `x_t = A(f_1, ..., f_{t-1})` is `A`'s own full
information play. Define the points `{x_t}` (Algorithm 22) by `x_1 ← A(∅)`,
`x_t ← A(g_1, ..., g_{t-1})` (`g_τ` substituted for `A` as the linear functional `y ↦ ⟪g_τ, y⟫`),
where each `g_t` is a vector valued random variable adapted to a filtration `𝓕` with
`E[g_t | x_1, f_1, ..., x_t, f_t] = ∇f_t(x_t)`. Then `E[Σ_{t=1}^T f_t(x_t)] - Σ_{t=1}^T f_t(u) ≤
E[B(g_1, ..., g_T)]`.

`𝓕` models the history "`x_1, f_1, ..., x_t, f_t`" available just before `g_t` is drawn: `x_t` is
`𝓕 t`-measurable and `g_t` is `𝓕 (t + 1)`-measurable (the `f_τ` are deterministic, so they add no
randomness to condition on). The empty history `A(∅)` is modeled by applying `A` to the
identically-zero cost sequence, since a non-anticipating `A`'s round-0 decision cannot depend on
any cost function's values. -/
theorem bandit_to_full_information_regret
    {Ω : Type*} [m0 : MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K : Set E) (T : ℕ) (u : E) (hu : u ∈ K)
    (f : ℕ → E → ℝ) (gradf : ℕ → E → E) (hf : ∀ t y, HasGradientAt (f t) (gradf t y) y)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsFirstOrderOnlineAlgorithm A)
    (B : (ℕ → E) → ℝ)
    (hB : ∀ (h : ℕ → E → ℝ) (grad' : ℕ → E),
      (∀ t, HasGradientAt (h t) (grad' t) (A h t)) →
      OnlineConvexOpt.FirstOrder.RegretT K h (fun t => A h t) T ≤ B grad')
    (𝓕 : ℕ → MeasurableSpace Ω) (hFmono : Monotone 𝓕) (hFle : ∀ t, 𝓕 t ≤ m0)
    (x g : ℕ → Ω → E)
    (hx0 : x 0 = fun _ => A (fun _ _ => (0 : ℝ)) 0)
    (hxstep : ∀ t : ℕ, x (t + 1) =
      fun ω => A (fun τ y => if τ ≤ t then inner ℝ (g τ ω) y else 0) (t + 1))
    (hxmeas : ∀ t, Measurable[𝓕 t] (x t))
    (hgmeas : ∀ t, Measurable[𝓕 (t + 1)] (g t))
    (hunbiased : ∀ t, condExp (𝓕 t) Prob (g t) =ᵐ[Prob] fun ω => gradf t (x t ω))
    (hfintegrable : ∀ t, Integrable (fun ω => f t (x t ω)) Prob)
    (hBintegrable : Integrable (fun ω => B (fun t => g t ω)) Prob) :
    (∫ ω, ∑ t ∈ Finset.range T, f t (x t ω) ∂Prob) - ∑ t ∈ Finset.range T, f t u ≤
      ∫ ω, B (fun t => g t ω) ∂Prob := by sorry

end OnlineConvexOpt.BanditConvex
