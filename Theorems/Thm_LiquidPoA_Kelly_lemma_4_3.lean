import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Lemma 4.3, p. 14: every vector in `𝕏ₙ` is an equilibrium of its affine game for a class-`𝒞` mechanism. -/
theorem lemma_4_3 {n : ℕ} (hn : 2 ≤ n) (M : Mechanism n)
    (hM : IsRAMechanism M) (hC : InClassC M)
    (s : Fin n → ℝ) (hs : InX s) :
    IsEquilibrium M (worstGame M s (⟨0, by omega⟩ : Fin n)) s := by sorry

end LiquidPoA.Kelly

