import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

/-- Theorem 4:1 (Hestenes–Stiefel 1952, p. 412). For every run of the cd-method with a
symmetric positive definite matrix `A`: (4:3a) the directions are mutually conjugate;
(4:3b) `rᵢ` is orthogonal to `p₀, …, pᵢ₋₁`; (4:3c) `(pᵢ, r₀) = (pᵢ, r₁) = ⋯ = (pᵢ, rᵢ)`;
(4:4) the step may be taken with `aᵢ = (pᵢ, r₀)/(pᵢ, Apᵢ)` in place of (4:1a). -/
theorem cd_conjugacy_relations {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) :
    (∀ i j, i ≠ j → p i ⬝ᵥ (A *ᵥ p j) = 0) ∧
    (∀ i j, j < i → p j ⬝ᵥ r i = 0) ∧
    (∀ i j, j ≤ i → p i ⬝ᵥ r j = p i ⬝ᵥ r 0) ∧
    (∀ i, x (i + 1) = x i + ((p i ⬝ᵥ r 0) / (p i ⬝ᵥ (A *ᵥ p i))) • p i) := by sorry

end ConjGrad.Termination
