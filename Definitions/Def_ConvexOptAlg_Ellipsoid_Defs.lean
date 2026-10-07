import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod
import Definitions.Def_LinearOptimization_Subgradient

namespace ConvexOptAlg.Ellipsoid

open Matrix

/-- The closed Euclidean ball `{x ∈ ℝⁿ : (x − z)⊤(x − z) ≤ ρ²}` of center `z` and radius `ρ`
(for `ρ ≥ 0`), written with the dot product because the sup norm is Mathlib's default norm on
`Fin n → ℝ`. Bubeck, arXiv:1405.4980v2, Ch. 2 preamble, p. 244 ("an Euclidean ball of radius R"). -/
def euclBall {n : ℕ} (z : Fin n → ℝ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {x | (x - z) ⬝ᵥ (x - z) ≤ ρ ^ 2}

/-- A convex body: a compact convex set with non-empty interior (Bubeck, Ch. 2 preamble, p. 244). -/
def IsConvexBody {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧ (interior X).Nonempty

/-- A run of the ellipsoid method (Bubeck, §2.2, pp. 249–250) on the constraint set `X` with
objective `f`, started from the Euclidean ball `E₀` of center `c0` and radius `R`
(`H₀ = R² Iₙ`). `c t` is the center, `H t` the matrix, `w t` the oracle answer at step `t`.

At every step `t` reached without a zero oracle answer (`w s ≠ 0` for all `s < t`):
* if `c t ∉ X`, `w t` is a nonzero separating vector: `X ⊆ {x : (x − c_t)⊤w_t ≤ 0}`;
* if `c t ∈ X`, `w t` is a subgradient of `f` at `c t` relative to `X`
  (`f(c_t) + w_t⊤(x − c_t) ≤ f(x)` for all `x ∈ X`, Definition 1.2);
* if `w t ≠ 0`, the next center and matrix are the update of Lemma 2.3 (2.5)–(2.6),
  `c_{t+1} = c_t − (1/(n+1)) H_t w_t / √(w_t⊤H_t w_t)` and
  `H_{t+1} = (n²/(n²−1)) (H_t − (2/(n+1)) H_t w_t w_t⊤H_t / (w_t⊤H_t w_t))`,
  i.e. Bertsimas–Tsitsiklis's `ellipsoidUpdateCenter`/`ellipsoidUpdateMatrix` with `a = −w_t`.

A zero answer can only be a subgradient at a center in `X`, which is then a minimizer of `f` on
`X`; the run stops there and later centers are unconstrained (the page's update would divide
by zero). -/
def IsEllipsoidRun {n : ℕ} (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (R : ℝ)
    (c0 : Fin n → ℝ) (c : ℕ → Fin n → ℝ) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (w : ℕ → Fin n → ℝ) : Prop :=
  c 0 = c0 ∧ H 0 = R ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) ∧
  ∀ t : ℕ, (∀ s < t, w s ≠ 0) →
    (c t ∉ X → w t ≠ 0 ∧ ∀ x ∈ X, (x - c t) ⬝ᵥ w t ≤ 0) ∧
    (c t ∈ X → LinearOptimization.IsSubgradientOn f X (w t) (c t)) ∧
    (w t ≠ 0 →
      c (t + 1) = LinearOptimization.ellipsoidUpdateCenter (c t) (H t) (-(w t)) ∧
      H (t + 1) = LinearOptimization.ellipsoidUpdateMatrix (H t) (-(w t)))

/-- `x` is an output of the ellipsoid method stopped after `t` iterations: a minimizer of `f`
over the centers queried in those iterations that lie in `X`, i.e.
`x ∈ argmin_{c ∈ {c₀, …, c_{t−1}} ∩ X} f(c)` (Bubeck, p. 250; see the indexing note of
Theorem 2.4). -/
def IsEllipsoidOutput {n : ℕ} (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (c : ℕ → Fin n → ℝ) (t : ℕ) (x : Fin n → ℝ) : Prop :=
  (∃ s < t, c s = x) ∧ x ∈ X ∧ ∀ s < t, c s ∈ X → f x ≤ f (c s)

/-- The scaled copy `X_ε = {(1 − ε)x∗ + εx : x ∈ X}` of `X` towards `x∗` (Bubeck, §2.1,
p. 246). -/
def scaledCopy {n : ℕ} (X : Set (Fin n → ℝ)) (xstar : Fin n → ℝ) (ε : ℝ) :
    Set (Fin n → ℝ) :=
  (fun x => (1 - ε) • xstar + ε • x) '' X

end ConvexOptAlg.Ellipsoid
