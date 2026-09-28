import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL

/-- The approximate cost of round `τ` in Follow the Approximate Leader (Fig. 3, version 1,
p. 180): with `∇_τ = ∇f_τ(x_τ)`,
`f̃_τ(z) = f_τ(x_τ) + ∇_τᵀ(z - x_τ) + (β/2) (z - x_τ)ᵀ ∇_τ ∇_τᵀ (z - x_τ)`.
The quadratic form `(z - x_τ)ᵀ ∇_τ ∇_τᵀ (z - x_τ)` equals `⟪∇_τ, z - x_τ⟫ ^ 2`. -/
noncomputable def approxLoss {n : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (β : ℝ) (τ : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f τ (x τ) + inner ℝ (gradient (f τ) (x τ)) (z - x τ)
    + β / 2 * (inner ℝ (gradient (f τ) (x τ)) (z - x τ)) ^ 2

/-- Follow the Approximate Leader, version 1 (Fig. 3, p. 180): `x 1 ∈ P` is arbitrary and, for
`t ≥ 2`, `x t` minimises `∑_{τ=1}^{t-1} f̃_τ` over `P`, where `f̃_τ = approxLoss f x β τ`. This
is Follow the Leader run on the approximate costs; `f̃_τ` only involves `x τ` with `τ < t`, so the
predicate on the whole trajectory is well founded. -/
def IsFTALRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (β : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  IsFTLRun P (approxLoss f x β) x

end LogRegretOCO.FTAL
