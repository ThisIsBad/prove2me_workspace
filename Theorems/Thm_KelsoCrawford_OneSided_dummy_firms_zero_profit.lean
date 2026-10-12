import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_KelsoCrawford_OneSided_Fictitious

namespace KelsoCrawford.OneSided

theorem dummy_firms_zero_profit {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (μ : W → ℝ → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hμ : ∀ i, StrictMono (μ i) ∧ Continuous (μ i))
    (A : Allocation W (Fin (Fintype.card W + 1)))
    (hcore : (fictitious v μ).IsStrictCore KelsoCrawford.ContinuousCore.anySalary A) :
    ∀ j, profit v (A.hired j) A.sal = 0 := by sorry

end KelsoCrawford.OneSided

