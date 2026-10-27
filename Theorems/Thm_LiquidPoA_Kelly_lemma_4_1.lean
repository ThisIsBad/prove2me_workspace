import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Lemma 4.1, p. 10: a minimum-welfare equilibrium is bounded by an affine worst-case game. -/
theorem lemma_4_1 {n : ℕ} (M : Mechanism n) (hM : IsRAMechanism M)
    (G : RAGame n) (hG : G.IsAdmissible)
    (hbad : 1 < gameLPoA M G) (s : Fin n → ℝ)
    (heq : IsEquilibrium M G s) (hs : InX s)
    (hmin : ∀ t, IsEquilibrium M G t → LW G (M.alloc s) ≤ LW G (M.alloc t)) :
    ∃ i : Fin n,
      gameLPoA M G ≤
        LW (worstGame M s i) (unitAlloc i) / LW (worstGame M s i) (M.alloc s) ∧
      LW (worstGame M s i) (unitAlloc i) / LW (worstGame M s i) (M.alloc s) =
        ratio M s i := by sorry

end LiquidPoA.Kelly

