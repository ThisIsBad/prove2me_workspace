import Mathlib

namespace BeckTeboulleMD.EMDA

/-- The distance-like function of (3.10), p. 170:
`B_ψ(x, y) = ψ(x) − ψ(y) − ⟨x − y, ∇ψ(y)⟩`, the pairing being the Fréchet derivative of `ψ` at the
**second** argument `y` applied to `x − y`. Lean's `fderiv` is `0` where `ψ` is not differentiable;
every statement using `bregman ψ x y` assumes differentiability of `ψ` at `y`. -/
noncomputable def bregman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (x y : E) : ℝ :=
  ψ x - ψ y - fderiv ℝ ψ y (x - y)

/-- A run of the subgradient algorithm with nonlinear projections (SANP), (3.11), p. 170, indexed from
`1` as on the page (`x 1` is the starting point `x¹`; `x 0` is unused). For every `k ≥ 1`: the step
size `t k` is positive, the iterate `x k` lies in `X`, `ψ` is differentiable at `x k`, and `x (k + 1)`
minimises `u ↦ ⟨u, f′(x^k)⟩ + (1 / t_k) B_ψ(u, x^k)` over `X`, where `g (x k)` is the subgradient
`f′(x^k)` returned by the oracle, viewed as a continuous linear functional. The predicate encodes the
paper's assumption that the SANP sequence is well defined (p. 171). -/
def IsSANPRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (g : E → E →L[ℝ] ℝ) (t : ℕ → ℝ) (x : ℕ → E) : Prop :=
  ∀ k, 1 ≤ k → 0 < t k ∧ x k ∈ X ∧ DifferentiableAt ℝ ψ (x k) ∧
    ∀ u ∈ X, g (x k) (x (k + 1)) + (1 / t k) * bregman ψ (x (k + 1)) (x k)
      ≤ g (x k) u + (1 / t k) * bregman ψ u (x k)

/-- The relative interior `int Δ = {x ∈ ℝⁿ : x_j > 0 ∀ j, ∑_j x_j = 1}` of the unit simplex
(Section 5, p. 173). The unit simplex `Δ` itself is Mathlib's `stdSimplex ℝ (Fin n)`. -/
def relIntSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j = 1}

/-- The entropy function `ψ_e(x) = ∑_j x_j ln x_j` of (5.27), p. 173, with `0 ln 0 = 0` (Lean's
`Real.log 0 = 0`). The page sets `ψ_e = +∞` off `Δ`; this formula is total, and every statement
evaluates it only on `Δ`. -/
noncomputable def entropy {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j, x j * Real.log (x j)

/-- A run of the entropic descent algorithm (EDA), p. 174, with constant step size `t`, indexed from
`1`: for every `s ≥ 1` and every coordinate `j`,
`x^{s+1}_j = x^s_j e^{−t g_j(x^s)} / ∑_i x^s_i e^{−t g_i(x^s)}`, where `g (x s)` is the subgradient
`f′(x^s)` returned by the oracle. -/
def IsEDARun {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) (x : ℕ → Fin n → ℝ) : Prop :=
  ∀ s, 1 ≤ s → ∀ j, x (s + 1) j =
    x s j * Real.exp (-(t * g (x s) j)) / ∑ i, x s i * Real.exp (-(t * g (x s) i))

end BeckTeboulleMD.EMDA
