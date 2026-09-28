import Mathlib

namespace CaiCandesShen.Convergence

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

/-- The objective `f_τ(X) = τ ‖X‖_* + ½ ‖X‖_F²` (§2.4, p. 1963; §3.1, p. 1964). -/
noncomputable def fτ {n₁ n₂ : ℕ} (τ : ℝ) (X : Mat n₁ n₂) : ℝ :=
  τ * nuclearNorm X + 1 / 2 * frobNorm X ^ 2

/-- The sampling projector `P_Ω`: the `(i, j)` entry of `P_Ω(X)` is `X_ij` if `(i, j) ∈ Ω` and
zero otherwise (§1.2, p. 1958). -/
def projΩ {n₁ n₂ : ℕ} (Ω : Finset (Fin n₁ × Fin n₂)) (X : Mat n₁ n₂) : Mat n₁ n₂ :=
  fun i j => if (i, j) ∈ Ω then X i j else 0

/-- `Z` is a subgradient of `f` at `X₀`, `Z ∈ ∂f(X₀)`, if `f(X) ≥ f(X₀) + ⟨Z, X - X₀⟩` for all `X`
(eq. (2.4), p. 1960). -/
def IsSubgradient {n₁ n₂ : ℕ} (f : Mat n₁ n₂ → ℝ) (X₀ Z : Mat n₁ n₂) : Prop :=
  ∀ X, f X₀ + frobInner Z (X - X₀) ≤ f X

end CaiCandesShen.Convergence
