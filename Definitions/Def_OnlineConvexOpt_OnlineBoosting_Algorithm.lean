import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.OnlineBoosting

variable {n : ℕ} {A : Type*}

/-- `IsOnlineBoostingRun K γ δ κ N T η a f W x fstage xplay` formalizes Algorithm 36 (p. 200,
PDF p. 222): `x t 0 = 0` (line 3, `x^0_t = 0`); at every stage `i ∈ [1,N]`,
`x t i = (1-η_i)x t (i-1) + η_i·(1/γ)·W t i` (line 5, `W t i` being weak learner `i`'s round-`t`
prediction `W_i(a_t)`); the final play `xplay t` is a metric projection of `x t N` onto `K`
(line 7, `x_t = Π_K[x^N_t]`); and `fstage t i` is the linear functional built from the extended
loss's gradient at the previous stage (line 10, `f^i_t(x) = ∇f̂_t(x^{i-1}_t)·x`, with
`f̂_t = X_{K,κ,δ}[f_t]`, line 8). Indexed from round `1` and stage `1`, matching the book. -/
def IsOnlineBoostingRun (K : Set (EuclideanSpace ℝ (Fin n))) (γ δ κ : ℝ) (N T : ℕ)
    (η : ℕ → ℝ) (a : ℕ → A) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (W : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → ℕ → EuclideanSpace ℝ (Fin n))
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (xplay : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ t : ℕ, 1 ≤ t → t ≤ T → x t 0 = 0) ∧
  (∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
    x t i = (1 - η i) • x t (i - 1) + η i • ((1 / γ) • W t i)) ∧
  (∀ t : ℕ, 1 ≤ t → t ≤ T → IsMetricProjection K (x t N) (xplay t)) ∧
  (∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N → ∀ v : EuclideanSpace ℝ (Fin n),
    HasGradientAt (Extension K κ δ (f t)) v (x t (i - 1)) →
    fstage t i = fun y => inner ℝ v y)

end OnlineConvexOpt.OnlineBoosting
