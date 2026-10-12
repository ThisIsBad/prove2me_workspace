import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

namespace DEpenoux.LinearProgram

theorem strict_vectorial_maximum (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hirr : ∀ J : Fin (σ + 1) → Fin (σ + 1), IsStrategy J →
      ∀ i k, ∃ n : ℕ, 0 < (stratMatrix p J ^ n) i k)
    (uStar : Fin (σ + 1) → ℝ)
    (huStar : BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar)
    (u : Fin (σ + 1) → ℝ) (hu : u ∈ setA p d lam) (hne : u ≠ uStar) :
    ∀ i, u i < uStar i := by sorry

end DEpenoux.LinearProgram

