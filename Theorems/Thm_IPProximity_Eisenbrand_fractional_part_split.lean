import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope

namespace IPProximity.Eisenbrand

/-- Proof of Theorem 3.3 (pp. 5:8–5:9): round a vertex `x` of the LP relaxation of (10) towards
an integer vector `z` (`rᵢ = ⌈xᵢ⌉` if `zᵢ > xᵢ`, `rᵢ = ⌊xᵢ⌋` otherwise) and let `{x} = x - r`.
Then `‖-A{x}‖∞ ≤ Δ·m`, and `-A{x}` is the sum of `m` integer vectors of `ℓ∞`-norm at most `Δ`. -/
theorem fractional_part_split {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) (z : Fin n → ℤ) :
    let r : Fin n → ℤ := fun i => if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋
    let frac : Fin n → ℝ := fun i => x i - (r i : ℝ)
    (∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m) ∧
      ∃ w : Fin m → Fin m → ℤ, (∀ j i, |w j i| ≤ (Δ : ℤ)) ∧
        ∀ i, ∑ j, (w j i : ℝ) = (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i := by sorry

end IPProximity.Eisenbrand

