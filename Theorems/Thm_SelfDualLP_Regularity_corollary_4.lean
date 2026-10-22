import Definitions.Def_SelfDualLP_Regularity_HLP

namespace SelfDualLP.Regularity

/-- Ye--Todd--Mizuno (1994), Corollary 4, p. 59. -/
theorem corollary_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n)
    (hw : IsSelfComplementary A b c w) (hκ : 0 < w.κ) :
    (¬ ∃ x, PrimalFeasible A b c x) ∨
      (¬ ∃ y, DualFeasible A c y) := by sorry

end SelfDualLP.Regularity

