import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.8, p. 73. The overbar in the book
denotes closed convex hull; `KD` is finite, so its convex hull is closed. -/
theorem convexHull_KD_eq_KS_eq_KM_eq_K_eq_P
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : IsInitialDistribution β) :
    convexHull ℝ (M.KD β) = M.KS β ∧
    M.KS β = M.KM β ∧
    M.KM β = M.K β ∧
    M.K β = M.feasibleFrequency β := by sorry

end KallenbergLP.Contracting

