import Mathlib

namespace FirstOrderOpt.Deterministic

/-- Proposition 3.1 (the one-step accelerated-gradient recursion). `f` is `L`-smooth (3.3.2) and
`μ`-generalized-strongly-convex w.r.t. the Bregman divergence `V` (3.3.3), via a gradient
selector `fGrad`. Given `(xPrev, xBarPrev) ∈ X × X`, form `xTilde` by (3.3.4), `xNew` by the
prox-mapping (3.3.5), and `xBarNew` by (3.3.6). If `q ≤ α` (3.3.7), `L(α-q)/(1-q) ≤ μ` (3.3.8)
and `Lq(1-α)/(1-q) ≤ 1/γ` (3.3.9), then for every `x ∈ X`,
`f(xBarNew) - f(x) + α(μ+1/γ)V(xNew,x) ≤ (1-α)[f(xBarPrev)-f(x)] + (α/γ)V(xPrev,x)`. `V` is
pinned down to a genuine Bregman divergence (nonnegative, three-point identity (3.2.6) via `dV`,
matching Lemma 3.5, p. 65): the proof needs the identity applied at both centers `xTilde` and
`xPrev` of the combined `μ·V(xTilde,·) + V(xPrev,·)` prox-mapping `hNewMin`, plus the
strong-convexity lower bound on `V` in bounding `‖dt‖²`. -/
theorem accelerated_one_step_recursion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (L μ : ℝ) (hL : 0 < L)
    (hμ : 0 ≤ μ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - (fGrad x) (y - x) ≤ (L / 2) * ‖y - x‖ ^ 2)
    (hStrConv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) + μ * V x y ≤ f y)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (xPrev xBarPrev xTilde xNew xBarNew : E)
    (hxPrev : xPrev ∈ X) (hxBarPrev : xBarPrev ∈ X) (hxTilde : xTilde ∈ X) (hxNew : xNew ∈ X)
    (hxBarNew : xBarNew ∈ X)
    (q γ α : ℝ) (hγ : 0 < γ)
    (hTilde : xTilde = (1 - q) • xBarPrev + q • xPrev)
    (hNewMin : ∀ x ∈ X, γ * (fGrad xTilde) xNew + μ * V xTilde xNew + V xPrev xNew ≤
      γ * (fGrad xTilde) x + μ * V xTilde x + V xPrev x)
    (hBarNew : xBarNew = (1 - α) • xBarPrev + α • xNew)
    (h7 : q ≤ α) (h8 : L * (α - q) / (1 - q) ≤ μ) (h9 : L * q * (1 - α) / (1 - q) ≤ 1 / γ) :
    ∀ x ∈ X, f xBarNew - f x + α * (μ + 1 / γ) * V xNew x ≤
      (1 - α) * (f xBarPrev - f x) + (α / γ) * V xPrev x := by sorry

end FirstOrderOpt.Deterministic
