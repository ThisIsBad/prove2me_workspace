import Mathlib

namespace CaiCandesShen.GeneralConvex

open Matrix

/-- Real `n₁ × n₂` matrices, the ambient space `ℝ^{n₁×n₂}` of the paper. -/
abbrev Mat (n₁ n₂ : ℕ) := Matrix (Fin n₁) (Fin n₂) ℝ

/-- The standard inner product `⟨X, Y⟩ = trace(X* Y) = ∑_{i,j} X_ij Y_ij` (§1.4, p. 1959). -/
def frobInner {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- The Frobenius norm `‖X‖_F = √⟨X, X⟩` (§1.4, p. 1959). -/
noncomputable def frobNorm {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : ℝ :=
  Real.sqrt (frobInner X X)

/-- The nuclear norm `‖X‖_*`: the sum of the singular values of `X`, where `X` is viewed as the
linear map `ℝ^{n₂} → ℝ^{n₁}` between Euclidean spaces (§1.4, p. 1959). -/
noncomputable def nuclearNorm {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues.sum (fun _ s => s)

/-- The objective `f_τ(X) = τ ‖X‖_* + ½ ‖X‖_F²` (§3.1, p. 1964). -/
noncomputable def fτ {n₁ n₂ : ℕ} (τ : ℝ) (X : Mat n₁ n₂) : ℝ :=
  τ * nuclearNorm X + 1 / 2 * frobNorm X ^ 2

/-- `Z` is a subgradient of `g` at `X₀`, `Z ∈ ∂g(X₀)`, if `g(X) ≥ g(X₀) + ⟨Z, X - X₀⟩` for all `X`
(eq. (2.4), p. 1960). -/
def IsSubgradient {n₁ n₂ : ℕ} (g : Mat n₁ n₂ → ℝ) (X₀ Z : Mat n₁ n₂) : Prop :=
  ∀ X, g X₀ + frobInner Z (X - X₀) ≤ g X

/-- The standard inner product `⟨u, v⟩ = ∑_i u_i v_i` on `ℝ^m`. -/
def dot {m : ℕ} (u v : Fin m → ℝ) : ℝ :=
  ∑ i, u i * v i

/-- The Euclidean norm `‖v‖ = √⟨v, v⟩` on `ℝ^m`. -/
noncomputable def eucNorm {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (dot v v)

end CaiCandesShen.GeneralConvex
