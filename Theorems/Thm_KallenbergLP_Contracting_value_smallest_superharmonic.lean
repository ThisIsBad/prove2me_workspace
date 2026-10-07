import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.1, p. 64. -/
theorem value_smallest_superharmonic
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M) :
    M.IsSuperharmonic M.value ∧
      ∀ w : E → ℝ, M.IsSuperharmonic w → ∀ i, M.value i ≤ w i := by sorry

end KallenbergLP.Contracting

