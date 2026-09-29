import Mathlib
import Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching

namespace Supermodularity.Matching

theorem isIncreasing_of_optimal_of_jointlyStrictlySupermodular
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : StrictlySupermodularOn (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    ∀ x : Fin m → ∀ i, X i, IsOptimalMatching f x → IsIncreasingMatching x := by sorry

end Supermodularity.Matching
