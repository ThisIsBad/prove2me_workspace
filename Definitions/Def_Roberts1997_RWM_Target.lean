import Mathlib

open MeasureTheory ProbabilityTheory

namespace Roberts1997.RWM

/-- The product density `π_n(x) = ∏_{i=1}^n f(x_i)` of (1.1), on `ℝ^n = Fin n → ℝ`
(the paper's component `i` is the Lean index `i - 1`). -/
noncomputable def targetDens (f : ℝ → ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, f (x i)

/-- The target measure `π_n(x) dx`: the product of `n` copies of `f(y) dy`. -/
noncomputable def target (f : ℝ → ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.withDensity (fun y => ENNReal.ofReal (f y)))

/-- The proposal variance `σ_n² = l²/(n - 1)`, computed in `ℝ`. -/
noncomputable def sigmaSq (n : ℕ) (l : ℝ) : ℝ := l ^ 2 / ((n : ℝ) - 1)

/-- The Gaussian proposal `q_n(x, ·) = N(x, σ_n² I_n)`, as the product of the independent
one-dimensional normals `N(x_i, σ_n²)`; its density is the displayed `q_n(x, y)`.
The variance is `σ_n²` coerced to `ℝ≥0` by `Real.toNNReal` (exact for `n ≥ 2`). -/
noncomputable def proposal (n : ℕ) (l : ℝ) (x : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal (x i) (sigmaSq n l).toNNReal)

/-- The acceptance function `α(x, y) = 1 ∧ π_n(y)/π_n(x)`. -/
noncomputable def accept (f : ℝ → ℝ) (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  min 1 (targetDens f n y / targetDens f n x)

/-- The first component `x_1` of a vector `x ∈ ℝ^n` (Lean index `0`); `0` when `n = 0`. -/
noncomputable def first {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if h : 0 < n then x ⟨0, h⟩ else 0

/-- The average acceptance rate
`a_n(l) = ∫∫ π_n(x) α(x, y) q_n(x, y) dx dy`, with `q_n(x, y) dy` written as the proposal
measure. -/
noncomputable def accRateN (f : ℝ → ℝ) (n : ℕ) (l : ℝ) : ℝ :=
  ∫ x, ∫ y, accept f n x y ∂(proposal n l x) ∂(target f n)

end Roberts1997.RWM
