import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

namespace KallenbergLP.OptTransient

/-- Theorem 3.3.4, printed p. 55. The bar denotes closed convex hull; K(D) is finite. -/
theorem occupation_sets {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hβ : ∀ i, 0 < β i) (hβsum : ∑ i, β i = 1) :
    convexHull ℝ (KPure m β) ⊆ KStationary m β ∧
    KStationary m β = KMarkov m β ∧
    KMarkov m β = K m β ∧
    K m β = feasibleSet m β := by sorry

end KallenbergLP.OptTransient

