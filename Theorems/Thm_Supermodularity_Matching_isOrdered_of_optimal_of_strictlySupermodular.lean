import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsOrderedMatching

namespace Supermodularity.Matching

theorem isOrdered_of_optimal_of_strictlySupermodular
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hfx : ∀ j : Fin m, StrictlySupermodularOn (fun x : ∀ i, X i => f x j) Set.univ) :
    ∀ x : Fin m → ∀ i, X i, IsOptimalMatching f x → IsOrderedMatching x := by sorry

end Supermodularity.Matching
