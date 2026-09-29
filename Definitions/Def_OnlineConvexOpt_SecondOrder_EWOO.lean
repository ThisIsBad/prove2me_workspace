import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.SecondOrder

variable {n : ℕ}

/-- The un-normalized exponential weight `w_t(x) = exp(-α Σ_{τ=1}^{t-1} f_τ(x))` of Algorithm 11
(EWOO), for cost functions `f` (0-indexed: `t` here is the book's round `t + 1`, so `Finset.range
t` sums the book's rounds `1, ..., t`, exactly the exponent of `w_{t+1}` in the book's own
0-indexed-shifted convention). -/
noncomputable def ewooWeight (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-α * ∑ τ ∈ Finset.range t, f τ x)

/-- `x` is a run of the Exponentially Weighted Online Optimizer (Algorithm 11, book p. 60, PDF
p. 82) on cost functions `f` over the convex set `K`, with parameter `α > 0`: at every round `t`,
`x t` is the `w_t`-weighted centroid of `K`,
`x_t = (∫_K x w_t(x) dx) / (∫_K w_t(x) dx)`. -/
def IsEWOO (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℕ, x t = (∫ y in K, ewooWeight α f t y ∂volume)⁻¹ •
    ∫ y in K, ewooWeight α f t y • y ∂volume

end OnlineConvexOpt.SecondOrder
