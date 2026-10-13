import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem lemma_3 {n : ℕ} (M : Model n) (hM : M.Standing) (i j : Fin n) (hij : j < i)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ t ∈ Finset.Icc 1 M.k, ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B → ε ≤ B i →
      M.f t z (B - ε • (Pi.single i 1 - Pi.single j 1)) ≤ M.f t z B) ∧
    (∀ t ≤ M.k, ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b → ε ≤ b i →
      M.g t z (b - ε • (Pi.single i 1 - Pi.single j 1)) ≤ M.g t z b) := by sorry

end TopkisRation.Levels

