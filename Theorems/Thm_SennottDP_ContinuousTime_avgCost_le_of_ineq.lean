import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal

namespace SennottDP.ContinuousTime

/-- Lemma 10.3.1 (p. 244). -/
theorem avgCost_le_of_ineq {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i)
    (Z : ℝ) (z : S → ℝ) (hz : BddBelow (Set.range z)) (h1015 : Ψ.Ineq1015 e Z z) :
    ∀ i, ((Ψ.avgCost (Ψ.ofStationary e he) i : ℝ≥0∞) : EReal) ≤ (Z : EReal) := by sorry

end SennottDP.ContinuousTime
