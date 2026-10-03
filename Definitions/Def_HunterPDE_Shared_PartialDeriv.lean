import Mathlib

namespace HunterPDE.Shared

/-- The partial derivative `∂ᵢu(x)` of `u : ℝⁿ → ℝ` in the `i`-th coordinate direction, as the
Fréchet derivative applied to the standard basis vector `eᵢ = EuclideanSpace.single i 1`.
Coordinates are 0-based (`i : Fin n`), the book's `1 ≤ i ≤ n` shifted by one. Where `u` is not
differentiable at `x`, Lean's `fderiv` is `0`. -/
noncomputable def partialDeriv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

/-- Iterated partial derivative along a list of coordinate directions:
`iteratedPartial u [i₁, i₂, …, iₘ] = ∂_{i₁} ∂_{i₂} ⋯ ∂_{iₘ} u` (the last direction is applied
first). The empty list gives `u` itself. -/
noncomputable def iteratedPartial {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    List (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ
  | [] => u
  | i :: l => partialDeriv (iteratedPartial u l) i

/-- The list of directions of a multi-index `α = (α₀, …, α_{n-1}) ∈ ℕⁿ`: `α₀` copies of `0`,
then `α₁` copies of `1`, …; its length is the order `|α| = ∑ i, α i`. -/
def multiIndexList {n : ℕ} (α : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (α i) i)

/-- The multi-index partial derivative `∂^α u = ∂₀^{α₀} ∂₁^{α₁} ⋯ ∂_{n-1}^{α_{n-1}} u` (Hunter,
*Notes on PDEs*, §1.8, with 0-based coordinates). For `α = 0` it is `u`. -/
noncomputable def multiDeriv {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  iteratedPartial u (multiIndexList α)

end HunterPDE.Shared
