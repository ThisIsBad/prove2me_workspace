import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (4.2), p. 108, first sentence: under condition (1.1), with `a > 0`,
almost surely `S_n ≤ a + 1` for every `n ≤ τ_a`. -/
theorem S_le_add_one_of_le_tau {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (a : ℝ) (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, (n : WithTop ℕ) ≤ tau a X ω → FreedmanTail.Bernstein.S X n ω ≤ a + 1 := by sorry

end FreedmanTail.Laplace

