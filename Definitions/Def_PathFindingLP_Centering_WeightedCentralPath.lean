import Mathlib

open Matrix

namespace PathFindingLP.Centering

variable {m n : ℕ}

/-- The slack vector `s(x) = A x - b` of the linear program `min { cᵀx : A x ≥ b }`
(Lee–Sidford, FOCS 2014, §II.A, p. 425). -/
def slack (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  A *ᵥ x - b

/-- The interior of the feasible region, `S⁰ = {x ∈ ℝⁿ : A x > b}` (componentwise strict),
(§II.A, p. 425). -/
def interiorS0 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 < slack A b x i}

/-- A pair `(x, w)` is feasible if `x ∈ S⁰` and `w ∈ ℝᵐ_{>0}` (§IV, p. 427). -/
def IsFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (w : Fin m → ℝ) : Prop :=
  x ∈ interiorS0 A b ∧ ∀ i, 0 < w i

/-- The weighted penalized objective `f_t(x, w) = t · cᵀx - ∑ᵢ wᵢ log s(x)ᵢ`, eq. (2), p. 427.
It is recorded for reference: the Newton step and the centrality below are given by the
explicit formulas of (3) and (4). -/
noncomputable def weightedObjective (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : ℝ :=
  t * (c ⬝ᵥ x) - ∑ i, w i * Real.log (slack A b x i)

/-- The matrix `Aᵀ S⁻¹ W S⁻¹ A` with `S = diag(s)`, `W = diag(w)`, where `S⁻¹` is the diagonal
matrix of the reciprocals `1 / sᵢ`. At `s = s(x)` it is the Hessian `∇²ₓₓ f_t(x, w)`. -/
noncomputable def weightedGram (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal w * diagonal (fun i => (s i)⁻¹) * A

/-- The gradient `∇ₓ f_t(x, w) = t c - Aᵀ S_x⁻¹ w`. -/
noncomputable def weightedGradient (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : Fin n → ℝ :=
  t • c - Aᵀ *ᵥ (diagonal (fun i => (slack A b x i)⁻¹) *ᵥ w)

/-- The Newton step, eq. (3), p. 428:
`h_t(x, w) = (Aᵀ S_x⁻¹ W S_x⁻¹ A)⁻¹ (t c - Aᵀ S_x⁻¹ w)`. -/
noncomputable def newtonStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : Fin n → ℝ :=
  (weightedGram A (slack A b x) w)⁻¹ *ᵥ weightedGradient A b c t x w

/-- The norm `‖v‖_M = √(vᵀ M v)` induced by a square matrix `M`. -/
noncomputable def matNorm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ (M *ᵥ v))

/-- The centrality, eq. (4), p. 428: the Newton step measured in the Hessian norm,
`δ_t(x, w) = ‖h_t(x, w)‖_{∇²ₓₓ f_t(x, w)}`. -/
noncomputable def centrality (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : ℝ :=
  matNorm (weightedGram A (slack A b x) w) (newtonStep A b c t x w)

end PathFindingLP.Centering
