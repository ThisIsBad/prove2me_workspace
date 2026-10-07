import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.3, printed p. 54: the stationary occupation map and its inverse. -/
theorem stationary_lp_correspondence {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hβ : ∀ i, 0 < β i) :
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      IsFeasible m β (stationaryOccupation m β π)) ∧
    (∀ x : StateAction m → ℝ, IsFeasible m β x →
      IsStationaryRule m (ruleOfOccupation m x) ∧
      IsTransient m (stationaryPolicy (ruleOfOccupation m x)) ∧
      stationaryOccupation m β (ruleOfOccupation m x) = x) ∧
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      ruleOfOccupation m (stationaryOccupation m β π) = π) ∧
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      (stationaryOccupation m β π ∈ (feasibleSet m β).extremePoints ℝ ↔
       IsPureRule m π)) := by sorry

end KallenbergLP.OptTransient

