import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem theorem_1 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0)
    (hb : (fun i => (b i : ℝ)) ∈ reducedCone B (ell N * ((detD B : ℝ) - 1))) :
    -- the optimal values z₁(b) of P1 and φ^B(b) of (4) exist
    ((∃ z₁ : ℝ, IsGreatest (lpValues B N cB cN (fun i => (b i : ℝ))) z₁) ∧
      (∃ φ : ℝ, IsGreatest (groupValues B N cB cN b) φ)) ∧
    -- (2): z₂(b) = z₁(b) + φ^B(b)
    (∀ z₁ φ : ℝ, IsGreatest (lpValues B N cB cN (fun i => (b i : ℝ))) z₁ →
      IsGreatest (groupValues B N cB cN b) φ → IsGreatest (ipValues B N cB cN b) (z₁ + φ)) ∧
    -- y^B(b): an optimal solution of (4) with Σ y_i ≤ D − 1
    (∃ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1) ∧
    -- (3): (B⁻¹(b − N y), y) is integral, nonnegative and optimal for P2
    (∀ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y → ∑ j, y j ≤ detD B - 1 →
      ∃ xB : Fin m → ℕ, B *ᵥ (fun i => (xB i : ℤ)) = b - N *ᵥ (fun j => (y j : ℤ)) ∧
        IsIPOptimal B N cB cN b xB y) ∧
    -- m-periodicity: (4) for b + α_i is (4) for b
    (∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b) := by sorry

end GomoryGroup.Rel

