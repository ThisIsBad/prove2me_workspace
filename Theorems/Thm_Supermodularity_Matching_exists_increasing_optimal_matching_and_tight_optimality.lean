import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching
import Definitions.Def_Supermodularity_Matching_IsTightMatching

namespace Supermodularity.Matching

theorem exists_increasing_optimal_matching_and_tight_optimality
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)] [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    (∃ x : Fin m → ∀ i, X i, IsIncreasingMatching x ∧ IsOptimalMatching f x) ∧
      ((∀ i, Fintype.card (X i) = m) →
        ∀ x : Fin m → ∀ i, X i, IsTightMatching x → IsIncreasingMatching x →
          ∀ y : Fin m → ∀ i, X i, IsTightMatching y → ∑ j, f (y j) j ≤ ∑ j, f (x j) j) := by sorry

end Supermodularity.Matching

