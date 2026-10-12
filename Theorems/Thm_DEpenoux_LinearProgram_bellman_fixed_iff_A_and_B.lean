import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

namespace DEpenoux.LinearProgram

theorem bellman_fixed_iff_A_and_B (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∀ u : Fin (σ + 1) → ℝ,
      BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u = u ↔
        u ∈ setA p d lam ∧ u ∈ setB p d lam) ∧
    (∀ u : Fin (σ + 1) → ℝ,
      u ∈ setB p d lam ↔
        ∃ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J ∧
          BertsekasDiscountedPolicyOp (model σ p d hp0 hp1) lam J u = u) := by sorry

end DEpenoux.LinearProgram

