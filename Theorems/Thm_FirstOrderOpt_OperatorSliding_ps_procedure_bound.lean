import Mathlib

namespace FirstOrderOpt.OperatorSliding

open scoped RealInnerProductSpace

/-- Proposition 8.1 (convergence of the prox-sliding, PS, procedure). `PS(g,x,β,T)` runs
`u_t = argmin_{u∈X}{g(u)+lh(u_{t-1},u)+βV(x,u)+βp_tV(u_{t-1},u)+χ(u)}` (8.1.17) and
`ũ_t = (1-θ_t)ũ_{t-1}+θ_tu_t` (8.1.18); `Φ(u) := g(u)+h(u)+βV(x,u)+χ(u)` (8.1.19).
`huThreePoint` is the three-point inequality that `u t` solving (8.1.17) yields by Lemma 3.5
(cited, not restated). `hMLip` is (8.1.3): `h(z) ≤ lh(y,z)+M‖z-y‖`. `hVstrong` is `V ≥ ‖·‖²/2`,
the strong-convexity property of the distance-generating function `ν` (Sect. 3.2), used together
with `hMLip` inside the proof to bound `-βp_tV(u_{t-1},u_t)+M‖u_t-u_{t-1}‖`. If `{p_t},{θ_t}`
satisfy (8.1.20) (`P_0=1`, `P_t=p_t(1+p_t)^{-1}P_{t-1}`, `θ_t=(P_{t-1}-P_t)/((1-P_t)P_{t-1})`),
then for any `t≥1` and `u∈X`, (8.1.21) holds. -/
theorem ps_procedure_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (g h chi : E → ℝ) (lh : E → E → ℝ) (V : E → E → ℝ)
    (x : E) (β M : ℝ) (hβ : 0 < β) (hM : 0 < M)
    (hVnonneg : ∀ a b, 0 ≤ V a b)
    (hVstrong : ∀ a b, (1 / 2) * ‖b - a‖ ^ 2 ≤ V a b)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ lh y z + M * ‖z - y‖)
    (Φ : E → ℝ) (hΦ : ∀ u, Φ u = g u + h u + β * V x u + chi u)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t)
    (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (u ũ : ℕ → E) (hu0 : u 0 = x) (hũ0 : ũ 0 = x) (hmem : ∀ t, u t ∈ X)
    (huThreePoint : ∀ t : ℕ, 1 ≤ t → ∀ w ∈ X,
      g (u t) + lh (u (t - 1)) (u t) + β * V x (u t) + chi (u t)
          + β * p t * V (u (t - 1)) (u t) ≤
        g w + lh (u (t - 1)) w + β * V x w + chi w + β * p t * V (u (t - 1)) w
          - β * (1 + p t) * V (u t) w)
    (hũrec : ∀ t : ℕ, 1 ≤ t → ũ t = (1 - θ t) • ũ (t - 1) + θ t • u t)
    (t : ℕ) (ht : 1 ≤ t) (w : E) (hw : w ∈ X) :
    β * (1 - P t)⁻¹ * V (u t) w + (Φ (ũ t) - Φ w) ≤
      P t * (1 - P t)⁻¹ *
        (β * V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 t, (p i ^ 2 * P (i - 1))⁻¹) := by sorry

end FirstOrderOpt.OperatorSliding
