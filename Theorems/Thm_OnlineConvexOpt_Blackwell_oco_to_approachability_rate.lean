import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_SupportFunction

namespace OnlineConvexOpt.Blackwell

/-- Theorem 13.7 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 211, PDF p. 233). Algorithm 37, with input OCO algorithm `A`, returns the
vector `ū_T = (1/T)∑_{t=1}^T u(x_t,y_t)` that approaches the set `S` at a rate of
`Dist(ū_T,S) ≤ Regret_T(A)/T`.

`S` (closed, bounded, convex, nonempty) is §13.2's standing hypothesis on the target set,
already carried by the mission's own goal theorem (`blackwell_approachability_sufficiency`).
`f_t(w) = w^⊤u_{t-1} - h_S(w)` (line 4, `u_0 := 0` since round `1`'s definition of `f_1` has no
preceding realized reward — matching the series' standing zero-history convention); `w_t =
A(f_1,...,f_{t-1})` (line 5); `x_t = O(w_t)` for a best-response oracle `O` satisfying (13.2)
(line 6, `hO`); `u_t = u(x_t,y_t)` (line 7). Since the `f_t` are concave, `A`'s guarantee (`hAreg`)
is stated for maximization: `max_{w⋆,‖w⋆‖≤1}∑f_t(w⋆) - ∑f_t(w_t) ≤ Regret_T(A)`. -/
theorem oco_to_approachability_rate
    {d : ℕ} (K2 : Set (EuclideanSpace ℝ (Fin d))) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSne : S.Nonempty)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hO : ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖ ≤ 1 → ∀ y ∈ K2,
      inner ℝ w (u (O w) y) - SupportFunction S w ≤ 0)
    (A : (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → ℕ → EuclideanSpace ℝ (Fin d))
    (RegretBoundA : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (y w x uvec : ℕ → EuclideanSpace ℝ (Fin d))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hy : ∀ t : ℕ, 1 ≤ t → t ≤ T → y t ∈ K2)
    (hu0 : uvec 0 = 0)
    (hf : ∀ t : ℕ, 1 ≤ t → t ≤ T → f t = fun v => inner ℝ v (uvec (t - 1)) - SupportFunction S v)
    (hw : ∀ t : ℕ, 1 ≤ t → t ≤ T → w t = A f t)
    (hx : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t = O (w t))
    (huvec : ∀ t : ℕ, 1 ≤ t → t ≤ T → uvec t = u (x t) (y t))
    (hAreg :
      (⨆ wstar ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
          ∑ t ∈ Finset.Icc 1 T, f t wstar) -
        ∑ t ∈ Finset.Icc 1 T, f t (w t) ≤ RegretBoundA) :
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, uvec t) S ≤ RegretBoundA / T := by sorry

end OnlineConvexOpt.Blackwell
