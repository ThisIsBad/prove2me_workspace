import Mathlib

namespace WeylPolyhedra.Shared

/-- Weyl (1935), §1, p. 291: the half-space `α ⬝ᵥ x ≥ 0`, given by a point `α ≠ 0` of the dual
space, is a *Stütze* (support) of the finite point system `S ⊆ ℝⁿ` when every point of `S`
satisfies the inequality. -/
def IsSupport {n : ℕ} (S : Finset (Fin n → ℝ)) (α : Fin n → ℝ) : Prop :=
  α ≠ 0 ∧ ∀ s ∈ S, 0 ≤ α ⬝ᵥ s

/-- Weyl (1935), §1, p. 291: a support `α ⬝ᵥ x ≥ 0` of `S` is an *extreme Stütze* (extreme
support) when equality `α ⬝ᵥ x = 0` holds for `n - 1` linearly independent points `x` of `S`
(linear independence in the homogeneous space `ℝⁿ`). Positive multiples of `α` give the same
extreme support (p. 291). -/
def IsExtremeSupport {n : ℕ} (S : Finset (Fin n → ℝ)) (α : Fin n → ℝ) : Prop :=
  IsSupport S α ∧
    ∃ T : Finset (Fin n → ℝ), T ⊆ S ∧ T.card = n - 1 ∧
      LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ t ∈ T, α ⬝ᵥ t = 0

end WeylPolyhedra.Shared
