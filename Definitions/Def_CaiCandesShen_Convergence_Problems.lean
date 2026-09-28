import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

open Matrix

/-- `Xs` solves problem (2.8), p. 1961: minimize `τ‖X‖_* + ½‖X‖_F²` subject to
`P_Ω(X) = P_Ω(M)`. -/
def IsSol28 {n₁ n₂ : ℕ} (τ : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) (M Xs : Mat n₁ n₂) : Prop :=
  projΩ Ω Xs = projΩ Ω M ∧ ∀ X, projΩ Ω X = projΩ Ω M → fτ τ Xs ≤ fτ τ X

/-- The linear map `𝒜 : ℝ^{n₁×n₂} → ℝ^m` given by the matrices `Aop i`:
`𝒜(X)_i = ⟨Aop i, X⟩` (every linear map into `ℝ^m` has this form). -/
def applyA {n₁ n₂ m : ℕ} (Aop : Fin m → Mat n₁ n₂) (X : Mat n₁ n₂) : Fin m → ℝ :=
  fun i => frobInner (Aop i) X

/-- The adjoint `𝒜*(y) = ∑_i y_i Aop i` of `applyA Aop`. -/
def adjA {n₁ n₂ m : ℕ} (Aop : Fin m → Mat n₁ n₂) (y : Fin m → ℝ) : Mat n₁ n₂ :=
  ∑ i, y i • Aop i

/-- The spectral norm `‖𝒜‖₂ := sup{‖𝒜(X)‖_ℓ₂ : ‖X‖_F = 1}` of the linear map `𝒜` (§4.2,
p. 1968). When `n₁ n₂ = 0` the unit sphere is empty and the value is `0`. -/
noncomputable def opNormA {n₁ n₂ m : ℕ} (Aop : Fin m → Mat n₁ n₂) : ℝ :=
  sSup ((fun X => Real.sqrt (∑ i, applyA Aop X i ^ 2)) '' {X : Mat n₁ n₂ | frobNorm X = 1})

/-- `Xs` solves problem (3.1), p. 1964: minimize `f_τ(X)` subject to `𝒜(X) = b`. -/
def IsSol31 {n₁ n₂ m : ℕ} (τ : ℝ) (Aop : Fin m → Mat n₁ n₂) (b : Fin m → ℝ) (Xs : Mat n₁ n₂) :
    Prop :=
  applyA Aop Xs = b ∧ ∀ X, applyA Aop X = b → fτ τ Xs ≤ fτ τ X

/-- The sampling operator extracting the `m` entries with indices `ω 0, …, ω (m − 1)`:
`𝒜(X)_i = X_{ω i}`, given by the matrix units `Aop i = e_{ω i}` (§3.1, p. 1964). -/
def samplingOp {n₁ n₂ m : ℕ} (ω : Fin m → Fin n₁ × Fin n₂) : Fin m → Mat n₁ n₂ :=
  fun i => Matrix.single (ω i).1 (ω i).2 1

end CaiCandesShen.Convergence
