import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.2, p. 64. -/
theorem stationary_frequency_bijection
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : ∀ i, 0 < β i) :
    (∀ q : StationaryRule E A, IsStationaryRule q →
      M.stationaryFrequency β q ∈ M.feasibleFrequency β) ∧
    (∀ x : StationaryRule E A, x ∈ M.feasibleFrequency β →
      IsStationaryRule (FiniteMDP.ruleOfFrequency x) ∧
      M.stationaryFrequency β (FiniteMDP.ruleOfFrequency x) = x) ∧
    (∀ q : StationaryRule E A, IsStationaryRule q →
      FiniteMDP.ruleOfFrequency (M.stationaryFrequency β q) = q) ∧
    (∀ q : StationaryRule E A, IsStationaryRule q →
      ((∃ f : PureRule E A, q = pureRule f) ↔
        M.stationaryFrequency β q ∈ (M.feasibleFrequency β).extremePoints ℝ)) := by sorry

end KallenbergLP.Contracting

