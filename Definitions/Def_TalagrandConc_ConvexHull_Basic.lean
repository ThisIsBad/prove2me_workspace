import Mathlib

namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Talagrand (1995), p. 123, §4.1: for `A ⊆ Ω^N` and `x ∈ Ω^N`,
`U_A(x) = { (s_i)_{i ≤ N} ∈ {0,1}^N ; ∃ y ∈ A, s_i = 0 ⇒ x_i = y_i }`,
seen as a subset of `ℝ^N`. -/
def U {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  {s | (∀ i, s i = 0 ∨ s i = 1) ∧ ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

/-- Talagrand (1995), p. 123, §4.1: `V_A(x)` is the convex hull of `U_A(x)` in `ℝ^N`. -/
def V {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  convexHull ℝ (U A x)

/-- Talagrand (1995), p. 123, §4.1: `f_c(A, x)` is the `ℓ²` (Euclidean) distance from `0` to
`V_A(x)`, i.e. `inf { (Σ_i s_i²)^{1/2} ; s ∈ V_A(x) }`. The Euclidean norm is written out
(Mathlib's norm on `Fin N → ℝ` is the sup norm). Values in `ℝ≥0∞`: for `A = ∅`,
`V_A(x) = ∅` and `f_c(A, x) = ⊤ = +∞`. -/
noncomputable def fc {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ s ∈ V A x, ENNReal.ofReal (Real.sqrt (∑ i, s i ^ 2))

/-- Talagrand (1995), Eq. (4.1.1), p. 123: the enlargement
`A_t^c = { x ∈ Ω^N ; f_c(A, x) ≤ t }` (the superscript `c` refers to "convexity"; this is not
a complement). The comparison is made in `EReal`, so `A_t^c = ∅` for `t < 0` and points with
`f_c(A, x) = +∞` never belong to it. -/
def enlarge {Ω : Type*} {N : ℕ} (A : Set (Fin N → Ω)) (t : ℝ) : Set (Fin N → Ω) :=
  {x | ((fc A x : ℝ≥0∞) : EReal) ≤ (t : EReal)}

/-- Talagrand (1995), Eq. (4.2.1), p. 126:
`ξ(α, u) = α (1 − u) log(1 − u) − (α + 1 − α u) log((1 + α − α u)/(1 + α))`.
At `u = 1` the term `(1 − u) log(1 − u)` is `0` (Mathlib's `Real.log 0 = 0`), so
`ξ(α, 1) = log(1 + α)`. Intended for `α ≥ 0` and `u ∈ [0, 1]`. -/
noncomputable def xi (α u : ℝ) : ℝ :=
  α * (1 - u) * Real.log (1 - u) - (α + 1 - α * u) * Real.log ((1 + α - α * u) / (1 + α))

/-- Talagrand (1995), p. 126, §4.2:
`f_α(A, x) = inf { Σ_{i ≤ N} ξ(α, s_i) ; s ∈ V_A(x) }`.
Values in `ℝ≥0∞` (for `α ≥ 0`, `ξ(α, ·) ≥ 0` on `[0, 1] ⊇` the coordinates of `V_A(x)`, so
`ENNReal.ofReal` loses nothing); for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def fAlpha {Ω : Type*} {N : ℕ} (α : ℝ) (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨅ s ∈ V A x, ENNReal.ofReal (∑ i, xi α (s i))

end TalagrandConc.ConvexHull
