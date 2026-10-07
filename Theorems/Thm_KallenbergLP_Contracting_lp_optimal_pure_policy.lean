import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.3, pp. 64–65. -/
theorem lp_optimal_pure_policy
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : ∀ i, 0 < β i) :
    (∃ x : StationaryRule E A, x ∈ M.feasibleFrequency β ∧
      ∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) ∧
    (∀ x : StationaryRule E A, x ∈ M.feasibleFrequency β →
      (∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) →
      ∀ f : PureRule E A, (∀ i, 0 < x i (f i)) →
        ∀ π : Policy E A, IsPolicy π →
          ∀ i, M.totalReward π i ≤ M.totalReward (purePolicy f) i) := by sorry

end KallenbergLP.Contracting

