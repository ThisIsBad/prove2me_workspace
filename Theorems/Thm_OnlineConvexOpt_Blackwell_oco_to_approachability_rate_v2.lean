import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_SupportFunction_v2



namespace OnlineConvexOpt.Blackwell

/-- Theorem 13.7 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 211, PDF p. 233). Algorithm 37, with input OCO algorithm `A` (playing in
the unit ball `K = B`), returns the vector `ū_T = (1/T)∑_{t=1}^T u(x_t,y_t)` that approaches
the set `S` at a rate of `Dist(ū_T,S) ≤ Regret_T(A)/T`.

`S` (closed, bounded, convex, nonempty) is §13.2's standing hypothesis on the target set.
`f_t(w) = w^⊤u_t - h_S(w)` with `u_t = u(x_t,y_t)` the round-`t` reward (line 7; `f_t` is the
loss revealed after `w_t` is chosen, as the proof's Eq. (13.3) `f_t(w_t) = w_t^⊤u(O(w_t),y_t)
- h_S(w_t) ≤ 0` and its "definition of `f_t`" step require); `w_t = A(f_1,...,f_{t-1}) ∈ B`
(line 5); `x_t = O(w_t)` for a best-response oracle `O` satisfying (13.2) (line 6, `hO`). Since
the `f_t` are concave, `A`'s guarantee (`hAreg`) is stated for maximization:
`max_{w⋆,‖w⋆‖≤1}∑f_t(w⋆) - ∑f_t(w_t) ≤ Regret_T(A)`.

Corrected version: the retired statement transcribed the pseudocode's index misprint
`f_t(w) = w^⊤u_{t-1} - h_S(w)` (Algorithm 37 line 4), contradicted by the book's own proof, so
its regret hypothesis constrained `u_0,...,u_{T-1}` while the conclusion was about
`u_1,...,u_T`; the index is now `u_t` and the artificial `u_0 = 0` is dropped. `SupportFunction`
is the `_v2` version (genuine maximum over `S`), the regret comparator is the genuine supremum
over the unit ball, and `A`'s plays are required to lie in its decision set `B` (so that the
oracle condition (13.2) applies to them). -/
theorem oco_to_approachability_rate_v2
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
    (hf : ∀ t : ℕ, 1 ≤ t → t ≤ T → f t = fun v => inner ℝ v (uvec t) - SupportFunction S v)
    (hw : ∀ t : ℕ, 1 ≤ t → t ≤ T → w t = A f t)
    (hwB : ∀ t : ℕ, 1 ≤ t → t ≤ T → ‖w t‖ ≤ 1)
    (hx : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t = O (w t))
    (huvec : ∀ t : ℕ, 1 ≤ t → t ≤ T → uvec t = u (x t) (y t))
    (hAreg :
      sSup ((fun wstar => ∑ t ∈ Finset.Icc 1 T, f t wstar) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) -
        ∑ t ∈ Finset.Icc 1 T, f t (w t) ≤ RegretBoundA) :
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, uvec t) S ≤ RegretBoundA / T := by sorry

end OnlineConvexOpt.Blackwell

