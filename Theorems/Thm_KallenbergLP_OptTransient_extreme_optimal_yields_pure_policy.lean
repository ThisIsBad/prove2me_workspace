import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.5, printed p. 57: an extreme LP optimum selects an optimal pure stationary policy. -/
theorem extreme_optimal_yields_pure_policy {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i)
    (x : StateAction m → ℝ)
    (hopt : IsOptimalLP m β x)
    (hext : x ∈ (feasibleSet m β).extremePoints ℝ)
    (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (hpositive : ∀ i, 0 < x ⟨i, f i⟩) :
    IsOptimalTransient m (purePolicy (fun i => (f i).1)) := by sorry

end KallenbergLP.OptTransient

