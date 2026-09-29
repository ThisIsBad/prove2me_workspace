import Mathlib

open Matrix

namespace StochLinOpt.UpperBound

/-- The squared confidence radius of ConfidenceBall₂ (Algorithm 3.1):
`β_t = max (128 n ln t ln (t² / δ), ((8/3) ln (t² / δ))²)`. -/
noncomputable def beta (n : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  max (128 * (n : ℝ) * Real.log (t : ℝ) * Real.log ((t : ℝ) ^ 2 / δ))
    ((8 / 3 * Real.log ((t : ℝ) ^ 2 / δ)) ^ 2)

/-- The design matrix `A_t = I + ∑_{τ=1}^{t-1} x_τ x_τᵀ` (the barycentric spanner is the standard
basis, so `A_1 = ∑ e_i e_iᵀ = I`). Rounds are numbered `1, 2, …`; `x 0` is never used. -/
noncomputable def designMatrix {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + ∑ τ ∈ Finset.Ico 1 t, vecMulVec (x τ) (x τ)

/-- The least-squares estimate `µ̂_t = A_t⁻¹ ∑_{τ=1}^{t-1} ℓ_τ x_τ` (so `µ̂_1 = 0`). -/
noncomputable def muHat {n : ℕ} (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : Fin n → ℝ :=
  (designMatrix x t)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 t, ℓ τ • x τ

/-- The confidence ellipsoid `B²_t = {ν : (ν - µ̂_t)ᵀ A_t (ν - µ̂_t) ≤ β_t}`, i.e.
`‖ν - µ̂_t‖_{2,A_t} ≤ √β_t`. -/
def confBall {n : ℕ} (δ : ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) : Set (Fin n → ℝ) :=
  {ν | (ν - muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (ν - muHat x ℓ t)) ≤ beta n δ t}

/-- The decision sequence `x` (with observed losses `ℓ`) is a run of ConfidenceBall₂(D, δ):
on every round `t ≥ 1`, `x_t ∈ D` and, for some `µ̃_t ∈ B²_t`, the pair `(x_t, µ̃_t)` minimises
`ν ⬝ᵥ y` jointly over `ν ∈ B²_t` and `y ∈ D`, i.e.
`x_t ∈ argmin_{y ∈ D} min_{ν ∈ B²_t} νᵀ y` with any tie-breaking. -/
def IsConfidenceBall2Run {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → x t ∈ D ∧
    ∃ μt ∈ confBall δ x ℓ t, ∀ ν ∈ confBall δ x ℓ t, ∀ y ∈ D, μt ⬝ᵥ x t ≤ ν ⬝ᵥ y

end StochLinOpt.UpperBound
