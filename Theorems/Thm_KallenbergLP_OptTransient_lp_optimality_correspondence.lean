import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.6, printed p. 58: the correspondence of Theorem 3.3.3 preserves optimality. -/
theorem lp_optimality_correspondence {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i) :
    (∀ π : StationaryRule n α, IsStationaryRule m π →
      IsOptimalTransient m (stationaryPolicy π) →
      IsOptimalLP m β (stationaryOccupation m β π)) ∧
    (∀ x : StateAction m → ℝ, IsOptimalLP m β x →
      IsOptimalTransient m (stationaryPolicy (ruleOfOccupation m x))) := by sorry

end KallenbergLP.OptTransient

