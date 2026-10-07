import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

/-- **Theorem 2.4** (Bubeck, arXiv:1405.4980v2, p. 250). Let `n ≥ 2`, `X ⊂ ℝⁿ` a convex body,
`f : X → [−B, B]` continuous and convex with a minimizer `x∗` on `X`, and `r, R > 0` with
`X` inside the Euclidean ball of center `c₀` and radius `R` and containing a Euclidean ball of
radius `r`. For every run of the ellipsoid method from `E₀ = B(c₀, R)` and every
`t ≥ 2n² log(R/r)` with `t ≥ 1`: some center queried in the first `t` iterations
(`c₀, …, c_{t−1}`) lies in `X`, and every output `x_t` (a minimizer of `f` over those centers
in `X`) satisfies `f(x_t) − min_X f ≤ (2BR/r) exp(−t/(2n²))`.

Indexing: the page writes `{c₁, …, c_t}`; the centers queried in `t` iterations, whose cuts
produce `E_t`, are `c₀, …, c_{t−1}`. -/
theorem theorem_2_4 {n : ℕ} (hn : 2 ≤ n) (X : Set (Fin n → ℝ)) (hX : IsConvexBody X)
    (f : (Fin n → ℝ) → ℝ) (hfcont : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    (B : ℝ) (hfB : ∀ x ∈ X, -B ≤ f x ∧ f x ≤ B)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (c0 : Fin n → ℝ) (hXR : X ⊆ euclBall c0 R)
    (z : Fin n → ℝ) (hXr : euclBall z r ⊆ X)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (c : ℕ → Fin n → ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ)
    (hrun : IsEllipsoidRun X f R c0 c H w)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : 2 * (n : ℝ) ^ 2 * Real.log (R / r) ≤ (t : ℝ)) :
    (∃ s < t, c s ∈ X) ∧
      ∀ x : Fin n → ℝ, IsEllipsoidOutput X f c t x →
        f x - f xstar ≤ 2 * B * R / r * Real.exp (-(t : ℝ) / (2 * (n : ℝ) ^ 2)) := by sorry

end ConvexOptAlg.Ellipsoid

